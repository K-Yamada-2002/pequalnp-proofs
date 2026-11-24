import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

namespace PlaneLocalPrice
open Finset

variable {N q : ℕ} (L : Fin N → Finset (Fin N))

def through (p : Fin N) := univ.filter (fun l => p ∈ L l)

private theorem partition_count (S : Finset (Fin N)) (f : Fin N → Finset (Fin N))
    (disj : (S : Set (Fin N)).PairwiseDisjoint f) (size : ∀ i ∈ S, (f i).card = q) :
    (S.biUnion f).card = S.card * q := by
  rw [card_biUnion disj]
  simp [Finset.sum_congr rfl size]

variable (order : N = q^2+q+1) (pos : 2 ≤ q)
    (size : ∀ l, (L l).card = q+1)
    (join : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, p ∈ L l ∧ p' ∈ L l)

include order pos size join in
theorem degree (p : Fin N) : (through L p).card = q+1 := by
  let f := fun l => (L l).erase p
  have disj : ((through L p) : Set (Fin N)).PairwiseDisjoint f := by
    intro l hl m hm neq
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨an,al⟩ := mem_erase.mp ha
    obtain ⟨_,am⟩ := mem_erase.mp hb
    exact neq ((join p a an.symm).unique ⟨(mem_filter.mp hl).2,al⟩ ⟨(mem_filter.mp hm).2,am⟩)
  have cover : (through L p).biUnion f = univ.erase p := by
    ext a
    simp only [mem_biUnion,mem_erase,mem_univ,and_true]
    constructor
    · rintro ⟨l,_,hal⟩
      exact (mem_erase.mp hal).1
    · intro h
      obtain ⟨l,hl,_⟩ := join p a h.symm
      exact ⟨l,mem_filter.mpr ⟨mem_univ _,hl.1⟩,mem_erase.mpr ⟨h,hl.2⟩⟩
  have each (l) (hl : l ∈ through L p) : (f l).card = q := by
    have he := card_erase_add_one ((mem_filter.mp hl).2)
    dsimp [f]
    rw [size l] at he
    omega
  have c := partition_count _ _ disj each
  rw [cover,card_erase_of_mem (mem_univ p),card_univ,Fintype.card_fin] at c
  have eq : (through L p).card * q = (q+1)*q := by
    rw [← c,order,Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega) eq

include order pos size join in
theorem meets (l m : Fin N) (ne : m ≠ l) : ∃ p ∈ L l, p ∈ L m := by
  let f := fun p => (through L p).erase l
  have disj : ((L l) : Set (Fin N)).PairwiseDisjoint f := by
    intro p hp a ha neq
    apply Finset.disjoint_left.mpr
    intro s hs hs'
    obtain ⟨sn,sp⟩ := mem_erase.mp hs
    have sa := (mem_erase.mp hs').2
    exact sn ((join p a neq).unique ⟨(mem_filter.mp sp).2,(mem_filter.mp sa).2⟩ ⟨hp,ha⟩)
  have each (p) (hp : p ∈ L l) : (f p).card = q := by
    have he := card_erase_add_one (s := through L p) (a := l) (mem_filter.mpr ⟨mem_univ _,hp⟩)
    rw [degree L order pos size join] at he
    dsimp [f]
    omega
  have sub : (L l).biUnion f ⊆ univ.erase l := by
    intro s hs
    obtain ⟨p,_,hp⟩ := mem_biUnion.mp hs
    exact mem_erase.mpr ⟨(mem_erase.mp hp).1,mem_univ _⟩
  have eq : (L l).biUnion f = univ.erase l := by
    apply Finset.eq_of_subset_of_card_le sub
    rw [partition_count _ _ disj each,size,card_erase_of_mem (mem_univ l),card_univ,Fintype.card_fin,order,Nat.add_sub_cancel]
    exact le_of_eq (by ring)
  obtain ⟨p,hp,hm⟩ := mem_biUnion.mp (eq.symm ▸ mem_erase.mpr ⟨ne,mem_univ m⟩)
  exact ⟨p,hp,(mem_filter.mp (mem_erase.mp hm).2).2⟩

-- An incident flag gives a maximal independent mask with q points and q lines.
include order pos size join in
theorem pencil_masks (o l : Fin N) (inc : o ∈ L l) :
    ∃ X B : Finset (Fin N), X.card = q ∧ B.card = q ∧
      (∀ p ∈ X, ∀ m ∈ B, p ∉ L m) ∧
      (∀ p ∉ X, ∃ m ∈ B, p ∈ L m) ∧ (∀ m ∉ B, ∃ p ∈ X, p ∈ L m) := by
  let X := (L l).erase o
  let B := (through L o).erase l
  have cx : X.card = q := by
    have h := card_erase_add_one inc
    dsimp [X]
    rw [size] at h
    omega
  have cb : B.card = q := by
    have h := card_erase_add_one (s := through L o) (a := l) (mem_filter.mpr ⟨mem_univ _,inc⟩)
    dsimp [B]
    rw [degree L order pos size join] at h
    omega
  refine ⟨X,B,cx,cb,?_,?_,?_⟩
  · intro p hp m hm hin
    obtain ⟨po,pl⟩ := mem_erase.mp hp
    obtain ⟨ml,om⟩ := mem_erase.mp hm
    exact ml ((join p o po).unique ⟨hin,(mem_filter.mp om).2⟩ ⟨pl,inc⟩)
  · intro p hp
    by_cases e : p = o
    · obtain ⟨m,hm⟩ := card_pos.mp (show 0 < B.card by omega)
      exact ⟨m,hm,e ▸ (mem_filter.mp (mem_erase.mp hm).2).2⟩
    · obtain ⟨m,hm,_⟩ := join p o e
      have ml : m ≠ l := fun eq => hp (mem_erase.mpr ⟨e,eq ▸ hm.1⟩)
      exact ⟨m,mem_erase.mpr ⟨ml,mem_filter.mpr ⟨mem_univ _,hm.2⟩⟩,hm.1⟩
  · intro m hm
    by_cases e : m = l
    · obtain ⟨p,hp⟩ := card_pos.mp (show 0 < X.card by omega)
      exact ⟨p,hp,e ▸ (mem_erase.mp hp).2⟩
    · obtain ⟨p,pl,pm⟩ := meets L order pos size join l m e
      have po : p ≠ o := fun eq => hm (mem_erase.mpr ⟨e,mem_filter.mpr ⟨mem_univ _,eq ▸ pm⟩⟩)
      exact ⟨p,mem_erase.mpr ⟨po,pl⟩,pm⟩

end PlaneLocalPrice
