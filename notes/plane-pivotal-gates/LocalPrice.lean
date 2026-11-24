import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PlaneLocalPrice

open PEqualNP.CircuitLowerBounds

variable {α : Type} [Fintype α] [DecidableEq α]

-- The default observation is the original assignment. Test i deletes line i.
abbrev Obs (α : Type) := Option α → Bool

def critical (w : Obs α) : Finset α :=
  Finset.univ.filter fun i => w none = true ∧ w (some i) = false

def Budget (P : Finset (Finset α)) (k : Nat) : Prop :=
  ∀ F ⊆ P, (F.biUnion id).card ≤ F.card + k

omit [Fintype α] in
private theorem addSet {P : Finset (Finset α)} {k : Nat} (h : Budget P k)
    (parents : Finset (Finset α)) (hp : parents ⊆ P) {d : Finset α}
    (hd : d ⊆ parents.biUnion id) {c : Nat} (hc : parents.card ≤ c+1) :
    Budget (insert d P) (k+c) := by
  intro F hf
  by_cases has : d ∈ F
  · let rest := F.erase d
    have sub : rest ∪ parents ⊆ P := by
      intro a ha
      rcases Finset.mem_union.mp ha with hr | hp'
      · have hr' := Finset.mem_erase.mp hr
        exact (Finset.mem_insert.mp (hf hr'.2)).resolve_left hr'.1
      · exact hp hp'
    have cov : F.biUnion id ⊆ (rest ∪ parents).biUnion id := by
      intro x hx
      obtain ⟨a,ha,hx⟩ := Finset.mem_biUnion.mp hx
      by_cases eq : a = d
      · subst a
        obtain ⟨b,hb,hx'⟩ := Finset.mem_biUnion.mp (hd hx)
        exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_union_right _ hb,hx'⟩
      · exact Finset.mem_biUnion.mpr ⟨a,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,ha⟩),hx⟩
    have upper := (Finset.card_le_card cov).trans (h _ sub)
    have size := Finset.card_union_le rest parents
    have erased : rest.card + 1 = F.card := Finset.card_erase_add_one has
    omega
  · have sub : F ⊆ P := fun a ha => (Finset.mem_insert.mp (hf ha)).resolve_left (fun e => has (e ▸ ha))
    exact (h F sub).trans (by omega)

def pool (w : List (Obs α)) : Finset (Finset α) :=
  insert ∅ (w.map critical).toFinset

def nextObs (w : List (Obs α)) (g : Gate) : Obs α := fun t =>
  g.op.eval (g.inputs.map fun i => (w.getD i (fun _ => false)) t)

def advance (w : List (Obs α)) (g : Gate) := w ++ [nextObs w g]

private theorem pool_step (w : List (Obs α)) (g : Gate) :
    pool (advance w g) = insert (critical (nextObs w g)) (pool w) := by
  ext a
  simp [pool,advance,or_left_comm]

private theorem read_mem (w : List (Obs α)) (i : Nat) :
    critical (w.getD i (fun _ => false)) ∈ pool w := by
  by_cases h : i < w.length
  · rw [List.getD_eq_getElem _ _ h]
    simp [pool,List.mem_map.mpr ⟨_,List.getElem_mem h,rfl⟩]
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [pool,critical]

-- Charge exactly when the new wire has a pivotal line and no operand contains
-- all its pivotal lines. For a legal binary gate this can only happen at AND.
def cost (w : List (Obs α)) (g : Gate) : Nat :=
  let d := critical (nextObs w g)
  if d = ∅ ∨ ∃ i ∈ g.inputs, d ⊆ critical (w.getD i (fun _ => false)) then 0 else 1

omit [Fintype α] in
theorem combine {P : Finset (Finset α)} {k : Nat} (h : Budget P k)
    {a b d : Finset α} (ha : a ∈ P) (hb : b ∈ P) (hd : d ⊆ a ∪ b) :
    Budget (insert d P) (k+1) := by
  apply addSet h {a,b} (by intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption) (by simpa using hd)
  exact (Finset.card_insert_le ..).trans (by simp)

omit [Fintype α] in
theorem constant_or_copy {P : Finset (Finset α)} {k : Nat} (h : Budget P k)
    {a d : Finset α} (ha : a ∈ P) (hd : d ⊆ a) : Budget (insert d P) k := by
  simpa using addSet h {a} (by simpa using ha) (by simpa using hd) (c := 0) (by simp)

private theorem crit_two (a b : Obs α) (op : GateOp) (ok : op = .and ∨ op = .or) :
    critical (fun t => op.eval [a t, b t]) ⊆ critical a ∪ critical b := by
  intro i hi
  rcases ok with rfl | rfl <;>
    cases ea : a none <;> cases eb : b none <;> cases fa : a (some i) <;> cases fb : b (some i) <;>
    simp_all [critical,GateOp.eval]

private theorem step_bound (w : List (Obs α)) (g : Gate) {k : Nat} (h : Budget (pool w) k)
    (ok : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2) :
    Budget (pool (advance w g)) (k + cost w g) := by
  rw [pool_step]
  unfold cost
  dsimp only
  split
  next cheap =>
    rw [Nat.add_zero]
    rcases cheap with empty | ⟨i,_,sub⟩
    · exact constant_or_copy h (Finset.mem_insert_self ..) (by rw [empty])
    · exact constant_or_copy h (read_mem w i) sub
  next expensive =>
    obtain ⟨op, ins⟩ := g
    change ins.length ≤ 2 at arity
    change op = .and ∨ op = .or at ok
    rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k',tail⟩⟩⟩
    · exfalso
      apply expensive
      left
      rcases ok with rfl | rfl <;> simp [nextObs,GateOp.eval,critical]
    · exfalso
      apply expensive
      right
      refine ⟨i,by simp,?_⟩
      intro x hx
      rcases ok with rfl | rfl <;> simpa [critical,nextObs,GateOp.eval] using hx
    · apply combine h (read_mem w i) (read_mem w j)
      exact crit_two _ _ op ok
    · simp at arity


def charge : List Gate → List (Obs α) → Nat
  | [], _ => 0
  | g :: gs, w => cost w g + charge gs (advance w g)

private theorem fold_bound (gs : List Gate) (w : List (Obs α)) {k : Nat}
    (h : Budget (pool w) k)
    (ok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    Budget (pool (gs.foldl advance w)) (k + charge gs w) := by
  induction gs generalizing w k with
  | nil => simpa [charge] using h
  | cons g gs ih =>
    have hg := ok g (by simp)
    simpa only [charge,List.foldl_cons,Nat.add_assoc] using
      ih (advance w g) (step_bound w g h hg.1 hg.2) (fun a ha => ok a (by simp [ha]))

private theorem initial_bound (w : List (Obs α))
    (h : ∀ a ∈ w, (critical a).card ≤ 1) : Budget (pool w) 0 := by
  intro F hf
  have small (a) (ha : a ∈ F) : a.card ≤ 1 := by
    have m := hf ha
    simp only [pool,Finset.mem_insert,List.mem_toFinset,List.mem_map] at m
    rcases m with rfl | ⟨v,hm,rfl⟩
    · simp
    · exact h v hm
  calc
    _ ≤ ∑ a ∈ F, (id a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ F, 1 := Finset.sum_le_sum small
    _ = _ := by simp

omit [Fintype α] [DecidableEq α] in
theorem map_read (w : List (Obs α)) (o : Nat) (t : Option α) :
    (w.map (fun v => v t)).getD o false = (w.getD o (fun _ => false)) t := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[o]? <;> rfl

omit [Fintype α] [DecidableEq α] in
theorem fold_eval (gs : List Gate) (w : List (Obs α)) (t : Option α) :
    (gs.foldl advance w).map (fun v => v t) =
      gs.foldl (fun vs g => vs ++ [g.op.eval (g.inputs.map (fun i => vs.getD i false))])
        (w.map (fun v => v t)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons,ih,advance,List.map_append,List.map_cons,List.map_nil,nextObs,map_read]

def outputObs (C : Circuit) (w : List (Obs α)) : Obs α :=
  fun t => C.eval (w.map (fun v => v t))

theorem pivotal_bound (C : Circuit) (w : List (Obs α))
    (simple : ∀ a ∈ w, (critical a).card ≤ 1) (mono : PEqualNP.MetaComplexity.Monotone2 C) :
    (critical (outputObs C w)).card ≤ charge C.gates w + 1 := by
  have ops (g) (hg : g ∈ C.gates) : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    simpa [Set.mem_insert_iff,Set.mem_singleton_iff] using mono g hg
  have budget := fold_bound C.gates w (initial_bound w simple) ops
  let final := C.gates.foldl advance w
  have ev : outputObs C w = final.getD C.output (fun _ => false) := by
    funext t
    unfold outputObs Circuit.eval Circuit.wires
    rw [← fold_eval,map_read]
  have mem : critical (outputObs C w) ∈ pool final := ev ▸ read_mem final C.output
  have last := budget {critical (outputObs C w)} (by simpa using mem)
  simpa [Nat.add_comm] using last

-- OR inherits the sensitivity bound of any operand true in the original test.
theorem or_free (w : List (Obs α)) (ins : List Nat) : cost w ⟨.or,ins⟩ = 0 := by
  unfold cost
  dsimp only
  apply ite_eq_left
  by_cases h : nextObs w ⟨.or,ins⟩ none = true
  · have hex : ∃ i ∈ ins, (w.getD i (fun _ => false)) none = true := by
      simpa [nextObs,GateOp.eval] using h
    obtain ⟨i,hi,hbase⟩ := hex
    right
    refine ⟨i,hi,?_⟩
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).2.2
    have off : (w.getD i (fun _ => false)) (some x) = false := by
      by_contra! hon
      have yes : nextObs w ⟨.or,ins⟩ (some x) = true := by
        simpa [nextObs,GateOp.eval] using
          (show ∃ j ∈ ins, (w.getD j (fun _ => false)) (some x) = true from ⟨i,hi,by simpa using hon⟩)
      simp_all
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbase,off⟩
  · left
    ext x
    simp [critical,h]

theorem charged_gate (w : List (Obs α)) (g : Gate) (ok : g.op = .and ∨ g.op = .or)
    (arity : g.inputs.length ≤ 2) (paid : cost w g = 1) :
    ∃ i j, g.op = .and ∧ g.inputs = [i,j] ∧
      ¬ critical (w.getD i (fun _ => false)) ⊆ critical (w.getD j (fun _ => false)) ∧
      ¬ critical (w.getD j (fun _ => false)) ⊆ critical (w.getD i (fun _ => false)) := by
  obtain ⟨op,ins⟩ := g
  change op = .and ∨ op = .or at ok
  rcases ok with rfl | rfl
  · have expensive : ¬ (critical (nextObs w ⟨.and,ins⟩) = ∅ ∨
        ∃ i ∈ ins, critical (nextObs w ⟨.and,ins⟩) ⊆ critical (w.getD i (fun _ => false))) := by
      intro cheap
      unfold cost at paid
      dsimp only at paid
      rw [ite_eq_left cheap] at paid
      contradiction
    rcases ins with _ | ⟨i,_ | ⟨j,_ | ⟨k,tail⟩⟩⟩
    · exact (expensive (Or.inl (by simp [critical,nextObs,GateOp.eval]))).elim
    · exact (expensive (Or.inr ⟨i,by simp,by simp [critical,nextObs,GateOp.eval]⟩)).elim
    · have hu := crit_two (w.getD i (fun _ => false)) (w.getD j (fun _ => false)) .and (Or.inl rfl)
      refine ⟨i,j,rfl,rfl,?_,?_⟩
      · intro sub
        exact expensive (Or.inr ⟨j,by simp,hu.trans (Finset.union_subset sub (by rfl))⟩)
      · intro sub
        exact expensive (Or.inr ⟨i,by simp,hu.trans (Finset.union_subset (by rfl) sub)⟩)
    · simp at arity
  · simp [or_free] at paid

end PlaneLocalPrice
