import Mathlib
import PEqualNP.Outside.L_meta_705

namespace CountingZeros

open PEqualNP.AndCount
open PEqualNP.Outside.L_meta_705_aux (gateVal_eq)

variable {n : ℕ} (C : AndCountCircuit n)

-- Record a single bit per AND gate, namely the value of its left side.
def signature (I : Finset (Fin n)) (i : Fin C.size) : Bool :=
  AndCountCircuit.sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I)

private theorem side_split {I J U : Finset (Fin n)} (hU : U ⊆ I ∪ J)
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) (i : Fin C.size)
    (ih : ∀ j < i, C.gateVal U j = true → C.gateVal I j = true ∨ C.gateVal J j = true)
    (hs : AndCountCircuit.sideTrue U B F i (C.gateVal U) = true) :
    AndCountCircuit.sideTrue I B F i (C.gateVal I) = true ∨
      AndCountCircuit.sideTrue J B F i (C.gateVal J) = true := by
  simp only [AndCountCircuit.sideTrue, decide_eq_true_eq] at hs ⊢
  rcases hs with ⟨v, hv, hu⟩ | ⟨j, hj, hji, ht⟩
  · rcases Finset.mem_union.mp (hU hu) with h | h
    · exact .inl (.inl ⟨v, hv, h⟩)
    · exact .inr (.inl ⟨v, hv, h⟩)
  · rcases ih j hji ht with h | h
    · exact .inl (.inr ⟨j, hj, hji, h⟩)
    · exact .inr (.inr ⟨j, hj, hji, h⟩)

private theorem gate_split {I J U : Finset (Fin n)} (hU : U ⊆ I ∪ J)
    (hs : signature C I = signature C J) (i : Fin C.size) :
    C.gateVal U i = true → C.gateVal I i = true ∨ C.gateVal J i = true := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    intro h
    rw [gateVal_eq] at h
    simp only [Bool.and_eq_true] at h
    have hl := side_split C hU _ _ i ih h.1
    have hr := side_split C hU _ _ i ih h.2
    change signature C I i = true ∨ signature C J i = true at hl
    have hI : signature C I i = true := hl.elim id (fun h => (congrFun hs i).trans h)
    have hJ : signature C J i = true := (congrFun hs i).symm.trans hI
    rcases hr with h | h
    · left
      rw [gateVal_eq, Bool.and_eq_true]
      exact ⟨hI, h⟩
    · right
      rw [gateVal_eq, Bool.and_eq_true]
      exact ⟨hJ, h⟩

theorem eval_split {I J U : Finset (Fin n)} (hU : U ⊆ I ∪ J)
    (hs : signature C I = signature C J) (ht : C.eval U = true) :
    C.eval I = true ∨ C.eval J = true := by
  simp only [AndCountCircuit.eval, decide_eq_true_eq] at ht ⊢
  rcases ht with ⟨v, hv, hu⟩ | ⟨j, hj, h⟩
  · rcases Finset.mem_union.mp (hU hu) with h | h
    · exact .inl (.inl ⟨v, hv, h⟩)
    · exact .inr (.inl ⟨v, hv, h⟩)
  · rcases gate_split C hU hs j h with h | h
    · exact .inl (.inr ⟨j, hj, h⟩)
    · exact .inr (.inr ⟨j, hj, h⟩)

-- Every rejected input whose one-vertex extensions are accepted has a distinct signature.
theorem bound (family : Finset (Finset (Fin n)))
    (test : ∀ I ∈ family, C.eval I = false ∧ ∀ u ∉ I, C.eval (insert u I) = true) :
    family.card ≤ 2 ^ C.size := by
  classical
  have subset {I J : Finset (Fin n)} (hi : I ∈ family) (hj : J ∈ family)
      (hs : signature C I = signature C J) : J ⊆ I := by
    intro u hu
    by_contra hn
    have incl : insert u I ⊆ I ∪ J := Finset.insert_subset
      (Finset.mem_union_right I hu) Finset.subset_union_left
    have h := eval_split C incl hs ((test I hi).2 u hn)
    simp [(test I hi).1, (test J hj).1] at h
  have inj : Function.Injective (fun I : family => signature C I.val) := by
    intro I J h
    exact Subtype.ext (Finset.Subset.antisymm (subset J.property I.property h.symm)
      (subset I.property J.property h))
  simpa using Fintype.card_le_of_injective _ inj

def independent (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  ∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w

def dominatesOutside (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  ∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v

noncomputable def maximalSets (G : SimpleGraph (Fin n)) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun I => independent G I ∧ dominatesOutside G I

private theorem mem_maximal {G : SimpleGraph (Fin n)} {I : Finset (Fin n)} :
    I ∈ maximalSets G ↔ independent G I ∧ dominatesOutside G I := by
  classical
  simp [maximalSets]

theorem graph_bound (G : SimpleGraph (Fin n))
    (test : ∀ I, independent G I → dominatesOutside G I →
      C.eval I = false ∧ ∀ u ∉ I, C.eval (insert u I) = true) :
    (maximalSets G).card ≤ 2 ^ C.size :=
  bound C _ fun I h => test I (mem_maximal.mp h).1 (mem_maximal.mp h).2

private theorem extend_independent (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (hs : independent G S) :
    ∃ I ∈ maximalSets G, S ⊆ I := by
  classical
  obtain ⟨I, hSI, hi⟩ := Finite.exists_le_maximal (p := independent G) hs
  refine ⟨I, mem_maximal.mpr ⟨hi.1, ?_⟩, hSI⟩
  intro u hu
  by_contra! noNeighbor
  have hnew : independent G (insert u I) := by
    intro a ha b hb
    rcases Finset.mem_insert.mp ha with hau | haI
    · rw [hau]
      rcases Finset.mem_insert.mp hb with hbu | hbI
      · rw [hbu]
        exact G.loopless.irrefl _
      · exact noNeighbor _ hbI
    · rcases Finset.mem_insert.mp hb with hbu | hbI
      · rw [hbu]
        exact fun h => noNeighbor _ haI h.symm
      · exact hi.1 _ haI _ hbI
  exact hu (hi.2 hnew (Finset.subset_insert u I) (Finset.mem_insert_self u I))

-- An induced matching supplies a different maximal independent set for every
-- choice of one endpoint per edge, including when other vertices are present.
theorem induced_matching_bound (G : SimpleGraph (Fin n)) {t : ℕ}
    (v : Fin t → Bool → Fin n) (edge : ∀ i, G.Adj (v i false) (v i true))
    (separate : ∀ i j, i ≠ j → ∀ b c, ¬ G.Adj (v i b) (v j c))
    (test : ∀ I, independent G I → dominatesOutside G I →
      C.eval I = false ∧ ∀ u ∉ I, C.eval (insert u I) = true) : t ≤ C.size := by
  classical
  let picks (f : Fin t → Bool) := Finset.univ.image fun i => v i (f i)
  have extn (f : Fin t → Bool) : ∃ I ∈ maximalSets G, picks f ⊆ I := by
    apply extend_independent
    intro a ha b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    by_cases h : i = j
    · subst j
      exact G.loopless.irrefl _
    · exact separate _ _ h _ _
  choose extend belongs includes using extn
  let mapped (f : Fin t → Bool) : maximalSets G := ⟨extend f, belongs f⟩
  have inj : Function.Injective mapped := by
    intro f g equal
    have same : extend f = extend g := congrArg Subtype.val equal
    funext i
    have h₁ : v i (f i) ∈ extend g := same ▸ includes f (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have h₂ : v i (g i) ∈ extend g := includes g (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hind := (mem_maximal.mp (belongs g)).1
    have nonadj := hind _ h₁ _ h₂
    cases hf : f i <;> cases hg : g i <;> simp_all [(edge i).symm]
  have hm : 2 ^ t ≤ (maximalSets G).card := by
    simpa using Fintype.card_le_of_injective _ inj
  exact (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp (hm.trans (graph_bound C G test))

end CountingZeros
