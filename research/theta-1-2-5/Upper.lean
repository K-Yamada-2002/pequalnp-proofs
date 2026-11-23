import PEqualNP.Defs

namespace ThetaOneTwoFive

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.and, [5, 13]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [15, 12]⟩,
    ⟨.or, [16, 14]⟩], 17⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2400000 in
theorem upper :
    ∃ C : Circuit, FanInTwo C ∧ C.size = 11 ∧
      ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 7,
          (u.val, v.val) ∈ ([(0, 1), (0, 2), (2, 1), (0, 3),
            (3, 4), (4, 5), (5, 6), (6, 1)] : List (ℕ × ℕ)) ∧
          x u = true ∧ x v = true := by
  refine ⟨circuit, ?_, rfl, ?_⟩
  · simp [FanInTwo, circuit]
  · decide +kernel

end ThetaOneTwoFive
