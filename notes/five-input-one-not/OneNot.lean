import Symmetry

namespace CircuitSymmetry
open PEqualNP.CircuitLowerBounds

def OneNot (gs : List Gate) : Prop := ∀ i j : Fin gs.length,
  (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j

theorem dual_not_source (n : ℕ) (g : Gate) (h : (dualGate n g).op = GateOp.not) : g.op = GateOp.not := by
  obtain ⟨op,args⟩ := g
  cases op <;> simp_all [dualGate]
  split at h <;> contradiction

theorem dual_get_source (n : ℕ) (gs : List Gate) (i : ℕ) (hi : i < gs.length)
    (h : ((dualList n gs)[i]'(by simpa [dual_length] using hi)).op = GateOp.not) :
    (gs[i]).op = GateOp.not := by
  induction gs generalizing n i with
  | nil => simp at hi
  | cons g gs ih =>
    cases i with
    | zero => exact dual_not_source n g h
    | succ i => exact ih (n+1) i (by simpa using hi) h

theorem dual_one (n : ℕ) (gs : List Gate) (h : OneNot gs) : OneNot (dualList n gs) := by
  intro i j hi hj
  have li : i.val < gs.length := by simpa [dual_length] using i.isLt
  have lj : j.val < gs.length := by simpa [dual_length] using j.isLt
  exact Fin.ext (congrArg (Fin.val (n := gs.length)) (h ⟨_,li⟩ ⟨_,lj⟩ (dual_get_source n gs _ li hi) (dual_get_source n gs _ lj hj)))

theorem permute_one {n : ℕ} (p : Equiv.Perm (Fin n)) (gs : List Gate) (h : OneNot gs) :
    OneNot (gs.map (renameGate p)) := by
  intro i j hi hj
  have li : i.val < gs.length := by simpa using i.isLt
  have lj : j.val < gs.length := by simpa using j.isLt
  exact Fin.ext (congrArg (Fin.val (n := gs.length)) (h ⟨_,li⟩ ⟨_,lj⟩ (by simpa [List.get_eq_getElem,renameGate] using hi)
    (by simpa [List.get_eq_getElem,renameGate] using hj)))

def noSaving {n : ℕ} (f : (Fin n → Bool) → Bool) :=
  ∀ s, realizesWith OneNot true s f → realizes false s f

-- This is the per-function implication used in the fifteen accepted shards.
theorem of_replacement {n : ℕ} {f : (Fin n → Bool) → Bool}
    (replace : ∀ (gs : List Gate) (o : ℕ),
      (∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) →
      OneNot gs → (∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = f x) →
      ∃ (ds : List Gate) (v : ℕ), (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
        ds.length ≤ gs.length ∧ ∀ x, Circuit.eval ⟨ds,v⟩ (List.ofFn x) = f x) : noSaving f := by
  intro s h
  obtain ⟨gs,o,cap,ops,one,ev⟩ := h
  obtain ⟨ds,v,mono,sz,he⟩ := replace gs o (by simpa [basic] using ops) one ev
  exact ⟨ds,v,sz.trans cap, by simpa [basic] using mono,trivial,he⟩

theorem transport_noSaving {n : ℕ} {f : (Fin n → Bool) → Bool}
    (hf : noSaving f) (pos : ∃ x, f x = true) (neg : ∃ x, f x = false)
    (p : Equiv.Perm (Fin n)) (flip : Bool) :
    noSaving (permute p (if flip then dual f else f)) := by
  intro s h
  have before := (permute_iff_with permute_one p).mp h
  apply (permute_iff p).mpr
  cases flip
  · exact hf s before
  · exact (dual_iff pos neg).mpr (hf s ((dual_iff_with dual_one pos neg).mp before))

end CircuitSymmetry
