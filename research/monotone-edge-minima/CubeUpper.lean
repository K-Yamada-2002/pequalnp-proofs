import PEqualNP.Defs.MetaComplexityLgpMono

namespace CubeUpper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit : Circuit :=
  ⟨[⟨.or, [3, 5]⟩,
    ⟨.or, [8, 6]⟩,
    ⟨.or, [8, 0]⟩,
    ⟨.or, [6, 0]⟩,
    ⟨.or, [3, 11]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.and, [9, 7]⟩,
    ⟨.and, [10, 1]⟩,
    ⟨.or, [15, 14]⟩,
    ⟨.and, [12, 2]⟩,
    ⟨.or, [17, 16]⟩,
    ⟨.and, [13, 4]⟩,
    ⟨.or, [19, 18]⟩], 20⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 13 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  refine ⟨circuit, ?_, rfl, ?_⟩
  · simp [Monotone2, circuit]
  · decide +kernel

end CubeUpper
