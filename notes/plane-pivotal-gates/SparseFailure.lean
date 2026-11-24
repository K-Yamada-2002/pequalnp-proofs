import LocalPrice
import Mathlib.Data.Fin.Basic

namespace PlaneLocalPrice
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def assignment {N : Nat} (X B : Finset (Fin N)) : Fin (N+N) → Bool :=
  Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (l ∈ B))

private theorem line_eq {N : Nat} (X B : Finset (Fin N)) (l : Fin N) :
    assignment X B (Fin.natAdd N l) = decide (l ∈ B) := Fin.addCases_right _

private theorem point_eq {N : Nat} (X B : Finset (Fin N)) (p : Fin N) :
    assignment X B (Fin.castAdd N p) = decide (p ∈ X) := Fin.addCases_left _

def afterDrop {N : Nat} (B : Finset (Fin N)) : Option (Fin N) → Finset (Fin N)
  | none => B
  | some i => B.erase i

def planeInputs {N : Nat} (X B : Finset (Fin N)) : List (Obs (Fin N)) :=
  List.ofFn fun k t => assignment X (afterDrop B t) k

private theorem simple_inputs {N : Nat} (X B : Finset (Fin N)) :
    ∀ a ∈ planeInputs X B, (critical a).card ≤ 1 := by
  intro a ha
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ha
  induction k using Fin.addCases with
  | left p => simp [critical,assignment,afterDrop]
  | right l =>
    have h : critical (fun t => assignment X (afterDrop B t) (Fin.natAdd N l)) ⊆ {l} := by
      intro i hi
      have mem := (Finset.mem_filter.mp hi).2
      simp only [afterDrop,line_eq,decide_eq_true_eq,Finset.mem_erase] at mem
      apply Finset.mem_singleton.mpr
      by_contra ne
      have yes : decide (l ≠ i ∧ l ∈ B) = true := decide_eq_true ⟨Ne.symm ne,mem.1⟩
      simp_all
    exact (Finset.card_le_card h).trans (by simp)

theorem plane_eval {N : Nat} (C : Circuit) (X B : Finset (Fin N)) (t : Option (Fin N)) :
    outputObs C (planeInputs X B) t = circuitFun (N+N) C (assignment X (afterDrop B t)) := by
  simp [outputObs,planeInputs,List.map_ofFn,circuitFun,Function.comp_def]

-- Each line of a minimal accepted set must be pivotal when deleted.
theorem minimal_price {N : Nat} (C : Circuit) (mono : Monotone2 C) (X B : Finset (Fin N))
    (on : circuitFun (N+N) C (assignment X B) = true)
    (minimal : ∀ i ∈ B, circuitFun (N+N) C (assignment X (B.erase i)) = false) :
    B.card ≤ charge C.gates (planeInputs X B) + 1 := by
  have sub : B ⊆ critical (outputObs C (planeInputs X B)) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (plane_eval C X B none).trans on,
      (plane_eval C X B (some i)).trans (minimal i hi)⟩
  exact (Finset.card_le_card sub).trans (pivotal_bound C _ (simple_inputs X B) mono)

-- No projective-plane axioms are required for this part of the lower bound.
theorem sparse_failure {N q : Nat} (I : Fin N → Fin N → Prop) (C : Circuit)
    (mono : Monotone2 C)
    (sound : ∀ z : Fin (N+N) → Bool,
      (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N+N) C z = false)
    (X B : Finset (Fin N)) (indep : ∀ p ∈ X, ∀ l ∈ B, ¬ I p l)
    (on : circuitFun (N+N) C (assignment X B) = true) :
    ∃ T ⊆ B, q < T.card ∧ circuitFun (N+N) C (assignment X T) = true ∧
      (∀ l ∈ T, circuitFun (N+N) C (assignment X (T.erase l)) = false) ∧
      T.card ≤ charge C.gates (planeInputs X T) + 1 := by
  classical
  let P (k : Nat) := ∃ T ⊆ B, circuitFun (N+N) C (assignment X T) = true ∧ T.card = k
  have ex : ∃ k, P k := ⟨B.card,B,Finset.Subset.rfl,on,rfl⟩
  obtain ⟨T,sub,acc,sz⟩ := Nat.find_spec ex
  have minimal (l) (hl : l ∈ T) : circuitFun (N+N) C (assignment X (T.erase l)) = false := by
    by_contra! bad
    have h' : P (T.erase l).card := ⟨_,(Finset.erase_subset ..).trans sub,by simpa using bad,rfl⟩
    have le := Nat.find_min' ex h'
    have sm := Finset.card_erase_lt_of_mem hl
    omega
  have large : q < T.card := by
    by_contra! small
    have sz' : (Finset.univ.filter (fun l : Fin N => assignment X T (Fin.natAdd N l) = true)) = T := by
      ext l
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,line_eq,decide_eq_true_eq]
    have neg := sound (assignment X T) (by rw [sz']; exact small) (by
      rintro ⟨p,l,incident,hp,hl⟩
      exact indep p (by simpa only [point_eq,decide_eq_true_eq] using hp) l (sub (by simpa only [line_eq,decide_eq_true_eq] using hl)) incident)
    simp_all
  exact ⟨T,sub,large,acc,minimal,minimal_price C mono X T acc minimal⟩

-- A uniform strict cap on join charges extends sparse soundness to all masks.
theorem sound_of_local_cap {N q : Nat} (I : Fin N → Fin N → Prop) (C : Circuit)
    (mono : Monotone2 C)
    (sound : ∀ z : Fin (N+N) → Bool,
      (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N+N) C z = false)
    (X B : Finset (Fin N)) (indep : ∀ p ∈ X, ∀ l ∈ B, ¬ I p l)
    (cap : ∀ T ⊆ B, charge C.gates (planeInputs X T) < q) :
    circuitFun (N+N) C (assignment X B) = false := by
  cases e : circuitFun (N+N) C (assignment X B) with
  | false => rfl
  | true =>
    obtain ⟨T,sub,large,_,_,price⟩ := sparse_failure I C mono sound X B indep e
    have small := cap T sub
    omega

end PlaneLocalPrice
