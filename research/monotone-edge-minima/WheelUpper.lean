import Mathlib
import PEqualNP.Defs

namespace WheelUpper

open PEqualNP.CircuitLowerBounds

private def wheel : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.or, [6, 5]⟩, ⟨.and, [0, 7]⟩,
    ⟨.or, [1, 3]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [9, 10]⟩,
    ⟨.or, [2, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [12, 13]⟩,
    ⟨.or, [8, 11]⟩, ⟨.or, [15, 14]⟩], 16⟩

private theorem mono : PEqualNP.MetaComplexity.Monotone2 wheel := by
  simp [PEqualNP.MetaComplexity.Monotone2, wheel]

private theorem size_eq : wheel.size = 11 := rfl

set_option maxRecDepth 10000 in
private theorem computes : ∀ x : Fin 6 → Bool, (wheel.eval (List.ofFn x) = true ↔
    ∃ u v : Fin 6, (u.val,v.val) ∈ ([(0,1),(1,2),(2,3),(3,4),(4,0),
      (0,5),(1,5),(2,5),(3,5),(4,5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) := by
  decide +kernel

theorem upper : ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 11 ∧
    ∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 6, (u.val,v.val) ∈ ([(0,1),(1,2),(2,3),(3,4),(4,0),
        (0,5),(1,5),(2,5),(3,5),(4,5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true) :=
  ⟨wheel, mono, size_eq, computes⟩

end WheelUpper
