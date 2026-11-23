import PEqualNP.Defs.MetaComplexityLgpMono

namespace PrismUpper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit : Circuit :=
  ⟨[⟨.or, [3, 2]⟩,
    ⟨.or, [3, 1]⟩,
    ⟨.or, [2, 0]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.and, [6, 9]⟩,
    ⟨.and, [8, 1]⟩,
    ⟨.or, [11, 10]⟩,
    ⟨.or, [7, 5]⟩,
    ⟨.and, [4, 13]⟩,
    ⟨.or, [14, 12]⟩], 15⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 10 ∧ (∀ x : Fin 6 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 6, (u.val, v.val) ∈ ([(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (0, 3), (1, 4), (2, 5)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  refine ⟨circuit, ?_, rfl, ?_⟩
  · simp [Monotone2, circuit]
  · decide +kernel

end PrismUpper
