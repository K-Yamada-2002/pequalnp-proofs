import LocalPrice

namespace PlaneLocalPrice
open PEqualNP.CircuitLowerBounds

variable {α : Type} [Fintype α] [DecidableEq α]

def isOr : GateOp → Bool
  | .or => true
  | _ => false

def rising (v : Obs α) := critical (fun t => !(v t))

private def upPool (w : List (Obs α)) := insert ∅ (w.map rising).toFinset

private theorem upRead (w : List (Obs α)) (i : Nat) :
    rising (w.getD i (fun _ => false)) ∈ upPool w := by
  by_cases h : i < w.length
  · rw [List.getD_eq_getElem _ _ h]
    simp [upPool,List.mem_map.mpr ⟨_,List.getElem_mem h,rfl⟩]
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [upPool,rising,critical]

-- An AND that switches from false to true inherits all its tests from any
-- operand that was originally false. A true baseline has no rising tests.
private theorem and_copy (w : List (Obs α)) (ins : List Nat) :
    ∃ a ∈ upPool w, rising (nextObs w ⟨.and,ins⟩) ⊆ a := by
  by_cases h : nextObs w ⟨.and,ins⟩ none = false
  · have hex : ∃ i ∈ ins, (w.getD i (fun _ => false)) none = false := by
      simpa [nextObs,GateOp.eval] using h
    obtain ⟨i,hi,base⟩ := hex
    refine ⟨_,upRead w i,?_⟩
    intro x hx
    have on : nextObs w ⟨.and,ins⟩ (some x) = true := by
      simpa [rising,critical] using (Finset.mem_filter.mp hx).2.2
    have allOn : ∀ j ∈ ins, (w.getD j (fun _ => false)) (some x) = true := by
      simpa [nextObs,GateOp.eval] using on
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simp only [base, Bool.not_false], by simp only [allOn i hi, Bool.not_true]⟩
  · refine ⟨∅,Finset.mem_insert_self ..,?_⟩
    simp [rising,critical,h]

private theorem upStep (w : List (Obs α)) (g : Gate) {k : Nat} (bud : Budget (upPool w) k)
    (ok : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2) :
    Budget (upPool (advance w g)) (k + (if isOr g.op then 1 else 0)) := by
  have eq : upPool (advance w g) = insert (rising (nextObs w g)) (upPool w) := by
    ext x
    simp [upPool,advance,or_left_comm]
  rw [eq]
  obtain ⟨op,ins⟩ := g
  change op = .and ∨ op = .or at ok
  rcases ok with rfl | rfl
  · obtain ⟨a,mem,sub⟩ := and_copy w ins
    simpa [isOr] using constant_or_copy bud mem sub
  · change Budget _ (k + 1)
    change ins.length ≤ 2 at arity
    rcases ins with _ | ⟨i,_ | ⟨j,_ | ⟨k',tail⟩⟩⟩
    · apply combine bud (a := ∅) (b := ∅) (Finset.mem_insert_self ..) (Finset.mem_insert_self ..)
      simp [rising,critical,nextObs,GateOp.eval]
    · apply combine bud (upRead w i) (upRead w i)
      simp [rising,critical,nextObs,GateOp.eval]
    · apply combine bud (upRead w i) (upRead w j)
      intro x hx
      simp only [rising,critical,Finset.mem_filter,Finset.mem_union,Finset.mem_univ,true_and] at hx ⊢
      cases e : w.getD i (fun _ => false) none <;> cases f : w.getD j (fun _ => false) none <;>
        cases e' : w.getD i (fun _ => false) (some x) <;> cases f' : w.getD j (fun _ => false) (some x) <;>
        simp_all [nextObs,GateOp.eval]
    · simp at arity

theorem rising_bound (C : Circuit) (w : List (Obs α))
    (simple : ∀ a ∈ w, (rising a).card ≤ 1) (mono : PEqualNP.MetaComplexity.Monotone2 C) :
    (rising (outputObs C w)).card ≤ (C.gates.filter (fun g => isOr g.op)).length + 1 := by
  have init : Budget (upPool w) 0 := by
    intro F hf
    have small (a) (ha : a ∈ F) : a.card ≤ 1 := by
      have mem := hf ha
      simp only [upPool,Finset.mem_insert,List.mem_toFinset,List.mem_map] at mem
      rcases mem with rfl | ⟨v,hm,rfl⟩
      · simp
      · exact simple v hm
    calc
      _ ≤ ∑ a ∈ F, (id a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ F, 1 := Finset.sum_le_sum small
      _ = _ := by simp
  have fold (gs : List Gate) (v : List (Obs α)) (k : Nat) (b : Budget (upPool v) k)
      (ok : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
      Budget (upPool (gs.foldl advance v)) (k + (gs.filter (fun g => isOr g.op)).length) := by
    induction gs generalizing v k with
    | nil => simpa using b
    | cons g gs ih =>
      have hg := ok g (by simp)
      have res := ih (advance v g) _ (upStep v g b hg.1 hg.2) (fun a ha => ok a (by simp [ha]))
      cases ig : isOr g.op <;> simpa [List.filter_cons,ig,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using res
  have bud := fold C.gates w 0 init (fun g hg => by
    simpa [Set.mem_insert_iff,Set.mem_singleton_iff] using mono g hg)
  let final := C.gates.foldl advance w
  have ev : outputObs C w = final.getD C.output (fun _ => false) := by
    funext t
    unfold outputObs Circuit.eval Circuit.wires
    rw [← fold_eval,map_read]
  have mem : rising (outputObs C w) ∈ upPool final := ev ▸ upRead final C.output
  have last := bud {rising (outputObs C w)} (by simpa using mem)
  simpa [Nat.add_comm] using last

end PlaneLocalPrice
