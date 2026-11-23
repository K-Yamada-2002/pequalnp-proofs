import PEqualNP.Defs
import Mathlib

namespace BowtieWeight
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (ℕ × ℕ) := [(0,1),(0,2),(1,2),(0,3),(0,4),(3,4)]

def wide (C : Circuit) (j : ℕ) : Bool := decide (∃ u v : Fin 5, u ≠ v ∧
  (C.wires (List.ofFn (fun i : Fin 5 => decide (i = u)))).getD (5+j) false = true ∧
  (C.wires (List.ofFn (fun i : Fin 5 => decide (i = v)))).getD (5+j) false = true)

def counts (C : Circuit) : ℕ × ℕ × ℕ :=
  let indices := List.range C.size
  let isAnd := fun (j : ℕ) => C.gates[j]?.any fun g =>
    match g.op with | .and => true | _ => false
  let isOr := fun (j : ℕ) => C.gates[j]?.any fun g =>
    match g.op with | .or => true | _ => false
  ((indices.filter isAnd).length,
   (indices.filter (fun j => isOr j && wide C j)).length,
   (indices.filter (fun j => isOr j && !wide C j)).length)

def correct (C : Circuit) : Prop := ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = true ↔
  ∃ u v : Fin 5, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true

def shortCircuit : Circuit :=
  ⟨[⟨.or,[1,2]⟩, ⟨.or,[3,4]⟩, ⟨.or,[5,6]⟩, ⟨.and,[0,7]⟩,
    ⟨.and,[1,2]⟩, ⟨.and,[3,4]⟩, ⟨.or,[9,10]⟩, ⟨.or,[8,11]⟩], 12⟩

def allWideCircuit : Circuit :=
  ⟨[⟨.or,[0,1]⟩, ⟨.or,[0,2]⟩, ⟨.or,[1,2]⟩, ⟨.and,[5,6]⟩, ⟨.or,[8,3]⟩,
    ⟨.or,[8,4]⟩, ⟨.or,[7,3]⟩, ⟨.and,[9,10]⟩, ⟨.or,[11,4]⟩, ⟨.and,[12,13]⟩], 14⟩

theorem short_witness : Monotone2 shortCircuit ∧ correct shortCircuit ∧
    counts shortCircuit = (3,3,2) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Monotone2, shortCircuit]
  · unfold correct
    decide +kernel
  · decide +kernel

theorem allWide_witness : Monotone2 allWideCircuit ∧ correct allWideCircuit ∧
    counts allWideCircuit = (3,7,0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Monotone2, allWideCircuit]
  · unfold correct
    decide +kernel
  · decide +kernel

end BowtieWeight
