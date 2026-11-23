import PEqualNP.Defs.MetaComplexityLgpMono

namespace HeawoodUpper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuit : Circuit :=
  ⟨[⟨.or, [8, 10]⟩,
    ⟨.or, [7, 14]⟩,
    ⟨.and, [0, 15]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [7, 17]⟩,
    ⟨.and, [1, 18]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [8, 20]⟩,
    ⟨.and, [2, 21]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [7, 23]⟩,
    ⟨.and, [3, 24]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [10, 26]⟩,
    ⟨.and, [4, 27]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [9, 29]⟩,
    ⟨.and, [5, 30]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [8, 32]⟩,
    ⟨.and, [6, 33]⟩,
    ⟨.or, [31, 34]⟩,
    ⟨.or, [28, 35]⟩,
    ⟨.or, [25, 36]⟩,
    ⟨.or, [22, 37]⟩,
    ⟨.or, [19, 38]⟩,
    ⟨.or, [16, 39]⟩], 40⟩

private def edges : List (Fin 14 × Fin 14) := [(0,7), (0,8), (0,10), (1,7), (1,9), (1,13), (2,8), (2,12), (2,13), (3,7), (3,11), (3,12), (4,10), (4,11), (4,13), (5,9), (5,10), (5,12), (6,8), (6,9), (6,11)]

private theorem edge_test (x : Fin 14 → Bool) :
    (edges.any fun e => x e.1 && x e.2) = true ↔
    ∃ u v : Fin 14, (u.val,v.val) ∈ (edges.map fun e => (e.1.val,e.2.val)) ∧
      x u = true ∧ x v = true := by
  simp only [List.any_eq_true, Bool.and_eq_true, List.mem_map]
  constructor
  · rintro ⟨⟨u,v⟩,h,hu,hv⟩
    exact ⟨u,v,⟨(u,v),h,rfl⟩,hu,hv⟩
  · rintro ⟨u,v,⟨⟨a,b⟩,h,hab⟩,hu,hv⟩
    obtain rfl : a = u := Fin.ext (congrArg Prod.fst hab)
    obtain rfl : b = v := Fin.ext (congrArg Prod.snd hab)
    exact ⟨(a,b),h,hu,hv⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
theorem upper : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 27 ∧ (∀ x : Fin 14 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 14, (u.val, v.val) ∈ ([(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  refine ⟨circuit, by simp [Monotone2, circuit], rfl, ?_⟩
  intro x
  apply Iff.trans _ (edge_test x)
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13] := rfl
  rw [hx]
  simp [Circuit.eval, Circuit.wires, circuit, GateOp.eval, List.getD, edges,
    List.foldl, List.all, List.any, and_or_left, or_assoc]

end HeawoodUpper
