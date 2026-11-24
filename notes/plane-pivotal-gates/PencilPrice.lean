import SparseFailure
import UpwardPrice
import Pencil
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic

namespace PlaneLocalPrice
open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem circuit_monotone {n : ℕ} (C : Circuit) (mono : Monotone2 C) (x y : Fin n → Bool)
    (xy : ∀ k, x k = true → y k = true) (on : circuitFun n C x = true) :
    circuitFun n C y = true := by
  let valid (v : Obs Unit) := v none = true → v (some ()) = true
  have read (w : List (Obs Unit)) (ok : ∀ v ∈ w, valid v) (j : ℕ) :
      valid (w.getD j (fun _ => false)) := by
    by_cases hj : j < w.length
    · rw [List.getD_eq_getElem _ _ hj]
      exact ok _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (by omega)]
      simp [valid]
  let w : List (Obs Unit) := List.ofFn (fun k t => t.elim (x k) (fun _ => y k))
  have fold (gs : List Gate) (v : List (Obs Unit)) (ok : ∀ a ∈ v, valid a)
      (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) : ∀ a ∈ gs.foldl advance v, valid a := by
    induction gs generalizing v with
    | nil => exact ok
    | cons g gs ih =>
      apply ih (advance v g) _ (fun a ha => ops a (by simp [ha]))
      intro a ha
      rcases List.mem_append.mp ha with old | new
      · exact ok _ old
      · have e : a = nextObs v g := List.mem_singleton.mp new
        subst a
        rcases ops g (by simp) with hand | hor
        · simpa [valid,nextObs,hand,GateOp.eval] using
            (show (∀ i ∈ g.inputs, v.getD i (fun _ => false) none = true) →
                  ∀ i ∈ g.inputs, v.getD i (fun _ => false) (some ()) = true from
              fun h i hi => read v ok i (h i hi))
        · simpa [valid,nextObs,hor,GateOp.eval] using
            (show (∃ i ∈ g.inputs, v.getD i (fun _ => false) none = true) →
                  ∃ i ∈ g.inputs, v.getD i (fun _ => false) (some ()) = true from
              fun ⟨i,hi,h⟩ => ⟨i,hi,read v ok i h⟩)
  have obs : valid (outputObs C w) := by
    have ev : outputObs C w = (C.gates.foldl advance w).getD C.output (fun _ => false) := by
      funext t
      unfold outputObs Circuit.eval Circuit.wires
      rw [← fold_eval,map_read]
    rw [ev]
    apply read _ (fold _ w ?_ ?_)
    · intro a ha
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ha
      exact xy k
    · intro g hg
      simpa [Set.mem_insert_iff,Set.mem_singleton_iff] using (mono g hg).1
  simpa [valid,outputObs,w,List.map_ofFn,Function.comp_def,Option.elim,circuitFun] using
    obs (by simpa [outputObs,w,List.map_ofFn,Function.comp_def,Option.elim,circuitFun] using on)

def bump {n : ℕ} (z : Fin n → Bool) (i k : Fin n) := z k || decide (k = i)

-- The input embedding permits counting several kinds of inactive coordinates
-- on the same baseline while ensuring that every input changes in at most one test.
theorem raise_price {n : ℕ} {α : Type} [Fintype α] [DecidableEq α] (f : α ↪ Fin n)
    (C : Circuit) (mono : Monotone2 C) (z : Fin n → Bool)
    (off : circuitFun n C z = false)
    (on : ∀ i, circuitFun n C (bump z (f i)) = true) :
    Fintype.card α ≤ (C.gates.filter (fun g => isOr g.op)).length + 1 := by
  let w : List (Obs α) := List.ofFn fun k => fun t => t.elim (z k) (fun i => bump z (f i) k)
  have simple (a) (ha : a ∈ w) : (rising a).card ≤ 1 := by
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ha
    have eq (i : α) (hi : i ∈ rising (fun t : Option α => t.elim (z k) (fun j => bump z (f j) k))) :
        k = f i := by
      have mem := (mem_filter.mp hi).2
      cases base : z k with
      | false => simpa [Option.elim,bump,base] using mem
      | true => simp [Option.elim,base] at mem
    apply card_le_one.mpr
    intro i hi j hj
    exact f.injective ((eq i hi).symm.trans (eq j hj))
  have full : rising (outputObs C w) = univ := by
    apply Finset.eq_univ_of_forall
    intro i
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_,?_⟩
    · simpa [outputObs,w,List.map_ofFn,Function.comp_def,Option.elim,circuitFun] using off
    · simpa [outputObs,w,List.map_ofFn,Function.comp_def,Option.elim,circuitFun] using on i
  have bound := rising_bound C w simple mono
  simpa [full] using bound

theorem pencil_or_lower {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hq : 2 ≤ q) (order : N = q^2+q+1)
    (size : ∀ l, (univ.filter (fun p => I p l)).card = q+1)
    (join : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (mono : Monotone2 C)
    (pairOn : ∀ p l : Fin N, I p l → circuitFun (N+N) C
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true)
    (sound : ∀ z : Fin (N+N) → Bool,
      (univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N+N) C z = false) :
    2 * q^2 + 1 ≤ (C.gates.filter (fun g => isOr g.op)).length := by
  let L := fun l : Fin N => univ.filter (fun p => I p l)
  have mem (p l) : p ∈ L l ↔ I p l := by simp [L]
  let l : Fin N := ⟨0,by omega⟩
  obtain ⟨o,inc⟩ := card_pos.mp (show 0 < (L l).card by change 0 < (univ.filter _).card; rw [size]; omega)
  obtain ⟨X,B,cx,cb,indep,pts,lines⟩ := pencil_masks L order hq size
    (fun p p' h => by simpa only [mem] using join p p' h) o l inc
  let z := assignment X B
  have zp (p : Fin N) : z (Fin.castAdd N p) = decide (p ∈ X) := Fin.addCases_left _
  have zl (m : Fin N) : z (Fin.natAdd N m) = decide (m ∈ B) := Fin.addCases_right _
  have off : circuitFun (N+N) C z = false := by
    apply sound
    · simp only [zl,decide_eq_true_eq,Finset.filter_mem_eq_inter,Finset.univ_inter,cb,le_refl]
    · rintro ⟨p,m,h,hp,hm⟩
      exact indep p (by simpa only [zp,decide_eq_true_eq] using hp) m
        (by simpa only [zl,decide_eq_true_eq] using hm) ((mem p m).mpr h)
  have acc (p m : Fin N) (h : p ∈ L m) (j : Fin (N+N))
      (hp : bump z j (Fin.castAdd N p) = true) (hm : bump z j (Fin.natAdd N m) = true) :
      circuitFun (N+N) C (bump z j) = true := by
    apply circuit_monotone C mono _ _ _ (pairOn p m ((mem p m).mp h))
    intro k hk
    rcases of_decide_eq_true hk with rfl | rfl <;> assumption
  let f : (↥(Xᶜ) ⊕ ↥(Bᶜ)) ↪ Fin (N+N) :=
    (Function.Embedding.sumMap (Function.Embedding.subtype _) (Function.Embedding.subtype _)).trans
      finSumFinEquiv.toEmbedding
  have on (i) : circuitFun (N+N) C (bump z (f i)) = true := by
    rcases i with p | m
    · obtain ⟨m,hm,hi⟩ := pts p (mem_compl.mp p.property)
      change circuitFun _ _ (bump z (Fin.castAdd N p.val)) = true
      exact acc p m hi _ (by simp [bump]) (by simp only [bump,zl,decide_eq_true hm,Bool.true_or])
    · obtain ⟨p,hp,hi⟩ := lines m (mem_compl.mp m.property)
      change circuitFun _ _ (bump z (Fin.natAdd N m.val)) = true
      exact acc p m hi _ (by simp only [bump,zp,decide_eq_true hp,Bool.true_or]) (by simp [bump])
  have count := raise_price f C mono z off on
  simp only [Fintype.card_sum,Fintype.card_coe,Finset.card_compl,Fintype.card_fin,cx,cb,order] at count
  omega

-- The first child of the submitted decomposition, using only public constants.
theorem pencil_child :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      Monotone2 C →
      (∀ p l : Fin N, I p l → circuitFun (N + N) C
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C z = false) →
      2 * q ^ 2 + 1 ≤ (C.gates.filter (fun g => g.op.eval [true, false])).length := by
  intro q N I dec C hq order lines pairs mono on sparse
  have equal : C.gates.filter (fun g => isOr g.op) =
      C.gates.filter (fun g => g.op.eval [true,false]) := by
    apply List.filter_congr
    intro g hg
    have ops : g.op = .and ∨ g.op = .or := by
      simpa [Set.mem_insert_iff,Set.mem_singleton_iff] using (mono g hg).1
    rcases ops with h | h <;> simp [h,isOr,GateOp.eval]
  rw [← equal]
  apply pencil_or_lower I C hq order (fun l => by simpa only [Fintype.card_subtype] using lines l) pairs mono on
  intro z small indep
  exact sparse z (by simpa only [Fintype.card_subtype] using small) indep

end PlaneLocalPrice
