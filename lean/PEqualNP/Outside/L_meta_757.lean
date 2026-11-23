import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104

namespace PEqualNP.Outside.L_meta_757_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [4, 5]⟩,
    ⟨.and, [3, 8]⟩, ⟨.or, [7, 9]⟩], 10⟩

theorem essential : ∀ i : Fin 6, ∃ x : Fin 6 → Bool,
    target (Function.update x i (!x i)) ≠ target x := by decide +kernel

theorem bound (s : ℕ) : HasCircuitSize 6 target s ↔ 5 ≤ s := by
  constructor
  · intro h
    have := Helpers.dep_lower 6 target essential s h
    omega
  · intro hs
    refine ⟨circuit, ?_, hs, ?_⟩
    · simp [FanInTwo, circuit]
    · decide +kernel

end PEqualNP.Outside.L_meta_757_aux

theorem PEqualNP.Outside.L_meta_757 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 3 && x 4) || (x 3 && x 5)) s ↔ 5 ≤ s := PEqualNP.Outside.L_meta_757_aux.bound
