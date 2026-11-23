import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_782_aux


-- A single outside assignment handles both Boolean labels at the output.
theorem boundary_bound {n k c : ℕ} (S A : Finset (Fin n)) (B : Finset ℕ)
    (single : ℕ → Finset (Fin n)) (eval : ℕ → Finset (Fin n) → Bool)
    (out : Finset (Fin n) → Bool)
    (small : ∀ b ∈ B, single b ⊆ S → (single b).card ≤ 1)
    (up : ∀ b a U, a ∈ single b → a ∈ U → eval b U = true)
    (transfer : ∀ a ∈ A, ∀ U, (∀ b ∈ B, a ∈ single b → eval b U = true) → out U = true)
    (reject : ∀ U, U.card ≤ k → Disjoint U S → out U = false)
    (ck : c ≤ k) (ca : c < A.card) : c < B.card := by
  classical
  by_contra! size
  -- Choose a single outside vertex for each exit that can see one.
  let bad := B.filter fun b => ¬ single b ⊆ S
  have witness (b : bad) : ∃ a, a ∈ single b.val ∧ a ∉ S := by
    have h := (Finset.mem_filter.mp b.property).2
    simpa only [Finset.not_subset] using h
  choose pick hp using witness
  let U := Finset.univ.image pick
  have hu : U.card ≤ k := calc
    U.card ≤ Fintype.card bad := by simpa [U] using Finset.card_image_le (s := Finset.univ) (f := pick)
    _ = bad.card := Fintype.card_coe _
    _ ≤ B.card := Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ k := size.trans ck
  have hd : Disjoint U S := by
    apply Finset.disjoint_left.mpr
    intro a ha
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    exact (hp b).2
  have off := reject U hu hd
  have exit (a : A) : ∃ b ∈ B, a.val ∈ single b ∧ eval b U = false := by
    by_contra! h
    have on := transfer a.val a.property U (by
      intro b hb ha
      exact Bool.eq_true_of_not_eq_false (h b hb ha))
    simp [off] at on
  choose f hf using exit
  have safe (a : A) : single (f a) ⊆ S := by
    by_contra hn
    let b : bad := ⟨f a, Finset.mem_filter.mpr ⟨(hf a).1, hn⟩⟩
    have hU : pick b ∈ U := Finset.mem_image_of_mem _ (Finset.mem_univ b)
    have on := up (f a) (pick b) U (hp b).1 hU
    simp [(hf a).2.2] at on
  let map (a : A) : B := ⟨f a, (hf a).1⟩
  have inj : Function.Injective map := by
    intro a a' eq
    have same : f a = f a' := congrArg Subtype.val eq
    apply Subtype.ext
    exact Finset.card_le_one.mp (small _ (hf a').1 (safe a')) _ (same ▸ (hf a).2.1) _ (hf a').2.1
  have count : A.card ≤ B.card := by simpa using Fintype.card_le_of_injective _ inj
  omega

private def moves {α : Type} (read : ℕ → α → Bool) (B : Finset ℕ) (x y : α) : Prop :=
  ∀ b ∈ B, read b x = true → read b y = true

theorem frontier {α : Type} (read : ℕ → α → Bool) (P : Finset ℕ)
    (step : ∀ w ∈ P, ∃ a < w, ∃ b < w, ∀ x y,
      (read a x = true → read a y = true) → (read b x = true → read b y = true) →
      read w x = true → read w y = true)
    (root : ℕ) :
    ∃ B : Finset ℕ, B.card ≤ 1 + P.card ∧ Disjoint B P ∧
      ∀ x y, moves read B x y → read root x = true → read root y = true := by
  classical
  have aux (h : ℕ) (T : Finset ℕ) : ∃ B : Finset ℕ,
      B.card ≤ T.card + (P.filter (· < h)).card ∧
      (∀ b ∈ B, b < h → b ∉ P) ∧ (∀ b ∈ B, h ≤ b → b ∈ T) ∧
      ∀ x y, moves read B x y → moves read T x y := by
    induction h generalizing T with
    | zero => exact ⟨T, by simp, by simp, fun _ hb _ => hb, fun _ _ h => h⟩
    | succ h ih =>
      have cardmono := Finset.card_le_card (show P.filter (· < h) ⊆ P.filter (· < h+1) from
        fun b hb => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hb).1, by
          have := (Finset.mem_filter.mp hb).2; omega⟩)
      by_cases hm : h ∈ P ∧ h ∈ T
      · obtain ⟨a, ha, b, hb, gate⟩ := step h hm.1
        let T' := insert a (insert b (T.erase h))
        have no : h ∉ T' := by simp [T', Nat.ne_of_gt ha, Nat.ne_of_gt hb]
        have cap : T'.card ≤ T.card + 1 := by
          have h₁ := Finset.card_insert_le a (insert b (T.erase h))
          have h₂ := Finset.card_insert_le b (T.erase h)
          have h₃ := Finset.card_erase_add_one hm.2
          change (insert a (insert b (T.erase h))).card ≤ T.card + 1
          omega
        have added : P.filter (· < h+1) = insert h (P.filter (· < h)) := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hp, hl⟩
            by_cases e : v = h
            · exact .inl e
            · exact .inr ⟨hp, by omega⟩
          · rintro (rfl | ⟨hp, hl⟩)
            · exact ⟨hm.1, by omega⟩
            · exact ⟨hp, by omega⟩
        have count : (P.filter (· < h+1)).card = (P.filter (· < h)).card + 1 := by
          rw [added, Finset.card_insert_of_notMem (by simp)]
        obtain ⟨B, sz, low, high, trans⟩ := ih T'
        refine ⟨B, by omega, ?_, ?_, ?_⟩
        · intro v hv lt
          by_cases e : v = h
          · subst v
            exact (no (high h hv le_rfl)).elim
          · exact low v hv (by omega)
        · intro v hv ge
          have hh := high v hv (by omega)
          rcases Finset.mem_insert.mp hh with rfl | hh
          · omega
          rcases Finset.mem_insert.mp hh with rfl | hh
          · omega
          exact (Finset.mem_erase.mp hh).2
        · intro x y ht w hw
          have move := trans x y ht
          by_cases e : w = h
          · subst w
            exact gate x y (move a (by simp [T'])) (move b (by simp [T']))
          · exact move w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨e, hw⟩)))
      · obtain ⟨B, sz, low, high, trans⟩ := ih T
        refine ⟨B, by omega, ?_, fun b hb hge => high b hb (by omega), trans⟩
        intro b hb lt
        by_cases eq : b = h
        · subst b
          exact fun hP => hm ⟨hP, high h hb le_rfl⟩
        · exact low b hb (by omega)
  let h := P.sup id + 1
  have below (w : ℕ) (hw : w ∈ P) : w < h :=
    Nat.lt_succ_of_le (Finset.le_sup (f := id) hw)
  obtain ⟨B, sz, low, _, trans⟩ := aux h {root}
  refine ⟨B, ?_, Finset.disjoint_left.mpr (by intro w hw hp; exact low w hw (below w hp) hp),
    fun x y hm => trans x y hm root (by simp)⟩
  have hsub := Finset.card_le_card (Finset.filter_subset (· < h) P)
  simp only [Finset.card_singleton] at sz
  omega


open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem foldl_step_length (G : List Gate) (w : List Bool) :
    (G.foldl step w).length = w.length + G.length := by
  induction G generalizing w with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_append_lt (l l' : List Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_of_length_le (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

theorem foldl_step_getD (G : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (G.foldl step w).getD i false = w.getD i false := by
  induction G generalizing w with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_append_lt _ _ _ hi

theorem foldl_step_getD_gate (G : List Gate) (w : List Bool) (t : ℕ) (ht : t < G.length) :
    (G.foldl step w).getD (w.length + t) false =
      (G[t]).op.eval ((G[t]).inputs.map fun i => ((G.take t).foldl step w).getD i false) := by
  have hsplit : G = G.take t ++ G[t] :: G.drop (t + 1) := by
    simp [List.take_append_drop]
  conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [foldl_step_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton, foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp only [step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp only [foldl_step_length, List.length_take, Nat.min_eq_left ht.le]; omega)]
  simp [foldl_step_length, Nat.min_eq_left ht.le]

theorem foldl_take_getD (G : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((G.take t).foldl step w).length) :
    (G.foldl step w).getD i false = ((G.take t).foldl step w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t G, List.foldl_append]
  exact foldl_step_getD _ _ _ hi

def read {n : ℕ} (C : Circuit) : ℕ → (Fin n → Bool) → Bool
  | 0, _ => false
  | r+1, x => (C.wires (List.ofFn x)).getD r false

def gateRange (n : ℕ) (C : Circuit) := Finset.Ico (n+1) (n+1+C.size)

def legal (C : Circuit) := ∀ g ∈ C.gates,
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def single {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun a => read C w (fun b => decide (b = a)) = true

theorem read_input {n : ℕ} (C : Circuit) (r : ℕ) (hr : r < n) (x : Fin n → Bool) :
    read C (r+1) x = x ⟨r,hr⟩ := by
  change (C.gates.foldl step _).getD r false = _
  rw [foldl_step_getD _ _ _ (by simpa using hr)]
  simp [List.getD_eq_getElem?_getD, hr]

theorem read_missing {n : ℕ} (C : Circuit) (r : ℕ) (hr : n+C.size ≤ r) (x : Fin n → Bool) :
    read C (r+1) x = false := by
  apply getD_of_length_le
  simpa [wires_eq, foldl_step_length, Circuit.size] using hr

theorem small_off_range {n : ℕ} (C : Circuit) (w : ℕ) (hw : w ∉ gateRange n C) :
    (single (n := n) C w).card ≤ 1 := by
  cases w with
  | zero => simp [single, read]
  | succ r =>
    by_cases h : r < n
    · apply Finset.card_le_one.mpr
      intro a ha b hb
      simp only [single, Finset.mem_filter, Finset.mem_univ, true_and, read_input C r h,
        decide_eq_true_eq] at ha hb
      exact ha.symm.trans hb
    · have hr : n + C.size ≤ r := by
        simp only [gateRange, Finset.mem_Ico, not_and] at hw
        have := hw (by omega)
        omega
      simp [single, read_missing C r hr]

def child (limit a : ℕ) := if a < limit then a+1 else 0

private theorem move_binary (op : GateOp) (hop : op = .and ∨ op = .or)
    (a b c d : Bool) (ha : a = true → c = true) (hb : b = true → d = true) :
    op.eval [a,b] = true → op.eval [c,d] = true := by
  rcases hop with rfl | rfl <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [GateOp.eval]

theorem step_at {n : ℕ} (C : Circuit) (ok : legal C) (w : ℕ) (hw : w ∈ gateRange n C) :
    ∃ a < w, ∃ b < w, ∀ x y : Fin n → Bool,
      (read C a x = true → read C a y = true) →
      (read C b x = true → read C b y = true) →
      read C w x = true → read C w y = true := by
  obtain ⟨lo, hi⟩ := Finset.mem_Ico.mp hw
  let t := w-(n+1)
  have ht : t < C.gates.length := by unfold t; change w < n+1+C.gates.length at hi; omega
  have weq : w = n+t+1 := by unfold t; omega
  let g := C.gates[t]
  obtain ⟨op, len⟩ := ok g (List.getElem_mem ht)
  obtain ⟨a,b,hab⟩ : ∃ a b, g.inputs = [a,b] := by
    rcases h : g.inputs with _ | ⟨a, tail⟩
    · simp [h] at len
    cases tail with
    | nil => simp [h] at len
    | cons b tail =>
      cases tail with
      | nil => exact ⟨a,b,rfl⟩
      | cons => simp [h] at len
  have earlier (r : ℕ) : child (n+t) r < w := by unfold child; split <;> omega
  refine ⟨_, earlier a, _, earlier b, ?_⟩
  have eval (x : Fin n → Bool) : read C w x =
      g.op.eval [read C (child (n+t) a) x, read C (child (n+t) b) x] := by
    rw [weq]
    change (C.gates.foldl step (List.ofFn x)).getD (n+t) false = _
    have hx : (List.ofFn x).length = n := by simp
    have equation := foldl_step_getD_gate C.gates (List.ofFn x) t ht
    rw [hx] at equation
    rw [equation]
    change g.op.eval (g.inputs.map _) = _
    rw [hab]
    have child_eq (r : ℕ) : ((C.gates.take t).foldl step (List.ofFn x)).getD r false =
        read C (child (n+t) r) x := by
      have l : ((C.gates.take t).foldl step (List.ofFn x)).length = n+t := by
        simp [foldl_step_length, Nat.min_eq_left ht.le]
      by_cases h : r < n+t
      · simp only [child, ite_eq_left h, read, wires_eq]
        exact (foldl_take_getD _ _ _ _ (by omega)).symm
      · rw [getD_of_length_le _ _ (by omega)]
        simp [child,h,read]
    simp only [List.map_cons, List.map_nil, child_eq]
  intro x y ha hb
  rw [eval x, eval y]
  exact move_binary _ op _ _ _ _ ha hb

theorem read_mono {n : ℕ} (C : Circuit) (ok : legal C) (x y : Fin n → Bool)
    (xy : ∀ a, x a = true → y a = true) (w : ℕ) :
    read C w x = true → read C w y = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hg : w ∈ gateRange n C
    · obtain ⟨a,ha,b,hb,step⟩ := step_at C ok w hg
      exact step x y (ih a ha) (ih b hb)
    · cases w with
      | zero => simp [read]
      | succ r =>
        by_cases hr : r < n
        · rw [read_input C _ hr, read_input C _ hr]
          exact xy _
        · have h : n + C.size ≤ r := by
            simp only [gateRange, Finset.mem_Ico, not_and] at hg
            have := hg (by omega)
            omega
          simp [read_missing C r h]

def marked {n : ℕ} (C : Circuit) (S : Finset (Fin n)) := (gateRange n C).filter fun w =>
  single (n := n) C w ⊆ S ∧ 1 < (single (n := n) C w).card

def point {n : ℕ} (U : Finset (Fin n)) (q : Fin n) := decide (q ∈ U)

theorem per_output {n k c : ℕ} (C : Circuit) (ok : legal C) (S : Finset (Fin n)) (o : ℕ)
    (reject : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ S, x q = false) → read C (o+1) x = false)
    (ck : c ≤ k) (ca : c < (single (n := n) C (o+1)).card) : c ≤ (marked C S).card := by
  classical
  obtain ⟨B, size, disj, trans⟩ := frontier (read (n := n) C) (marked C S)
    (fun w hw => step_at C ok w (Finset.mem_filter.mp hw).1) (o+1)
  have small (b : ℕ) (hb : b ∈ B) (sub : single (n := n) C b ⊆ S) : (single (n := n) C b).card ≤ 1 := by
    by_cases hr : b ∈ gateRange n C
    · by_contra! large
      exact Finset.disjoint_left.mp disj hb (Finset.mem_filter.mpr ⟨hr, sub, large⟩)
    · exact small_off_range C b hr
  apply Nat.le_of_lt_succ
  have hbound := boundary_bound (k := k) (c := c) S (single (n := n) C (o+1)) B (single (n := n) C)
    (fun b U => read C b (point U)) (fun U => read C (o+1) (point U)) small
  have up (b : ℕ) (a : Fin n) (U : Finset (Fin n)) (ha : a ∈ single (n := n) C b) (hu : a ∈ U) :
      read C b (point U) = true := by
    apply read_mono C ok (fun q => decide (q=a)) (point U) _ b (Finset.mem_filter.mp ha).2
    intro q hq
    have eq : q = a := of_decide_eq_true hq
    simpa [point, eq] using hu
  have transfer (a : Fin n) (ha : a ∈ single (n := n) C (o+1)) (U : Finset (Fin n))
      (cover : ∀ b ∈ B, a ∈ single (n := n) C b → read C b (point U) = true) :
      read C (o+1) (point U) = true := by
    apply trans (fun q => decide (q=a)) (point U) _ (Finset.mem_filter.mp ha).2
    exact fun b hb h => cover b hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have off (U : Finset (Fin n)) (hu : U.card ≤ k) (dis : Disjoint U S) :
      read C (o+1) (point U) = false := by
    apply reject
    · simpa [point] using hu
    · intro q hq
      have hn : q ∉ U := fun hh => Finset.disjoint_left.mp dis hh hq
      simp [point,hn]
  have h := hbound up transfer off ck ca
  omega

end PEqualNP.Outside.L_meta_782_aux

theorem PEqualNP.Outside.L_meta_782 : ∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true → p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (Finset.univ.filter (fun a : Fin n => (C.wires (List.ofFn (fun b : Fin n => decide (b = a)))).getD (o i) false = true)).card) → ∑ i : Fin m, c i ≤ C.size := by
  intro n m k S C o c intersections _ ok _ reject ck ca
  classical
  let P := fun i => PEqualNP.Outside.L_meta_782_aux.marked C (S i)
  have each (i : Fin m) : c i ≤ (P i).card :=
    PEqualNP.Outside.L_meta_782_aux.per_output C ok (S i) (o i) (reject i) (ck i) (ca i)
  have pairwise : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint P := by
    intro i _ j _ hne
    apply Finset.disjoint_left.mpr
    intro w hi hj
    have hx := (Finset.mem_filter.mp hi).2
    have hy := (Finset.mem_filter.mp hj).2
    have sub : PEqualNP.Outside.L_meta_782_aux.single C w ⊆ S i ∩ S j :=
      fun a ha => Finset.mem_inter.mpr ⟨hx.1 ha, hy.1 ha⟩
    exact (Nat.not_lt_of_ge ((Finset.card_le_card sub).trans (intersections i j hne))) hx.2
  calc
    ∑ i, c i ≤ ∑ i, (P i).card := Finset.sum_le_sum (fun i _ => each i)
    _ = (Finset.univ.biUnion P).card := (Finset.card_biUnion pairwise).symm
    _ ≤ (PEqualNP.Outside.L_meta_782_aux.gateRange n C).card := by
      apply Finset.card_le_card
      intro w hw
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp hi).1
    _ = C.size := by simp [PEqualNP.Outside.L_meta_782_aux.gateRange]
