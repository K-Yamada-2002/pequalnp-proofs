import Mathlib.Data.List.GetD
import PEqualNP.Defs.CircuitLowerBounds

namespace CircuitSymmetry
open PEqualNP.CircuitLowerBounds

def basic (allowNot : Bool) (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ (allowNot = true ∧ g.op = .not)) ∧ g.inputs.length ≤ 2

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (w.getD · false))]

theorem run_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, step]; omega

-- A missing original wire reads false. In a dual AND it is neutral, but in
-- a dual OR it forces the value true, which the empty AND supplies.
def dualGate (n : ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => if g.inputs.all (· < n) then ⟨.or,g.inputs⟩ else ⟨.and,[]⟩
  | .or => ⟨.and,g.inputs.filter (· < n)⟩
  | .not => match g.inputs with
    | i :: _ => if i < n then ⟨.not,[i]⟩ else ⟨.or,[]⟩
    | [] => ⟨.or,[]⟩
  | _ => ⟨.or,[]⟩

def dualList (n : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => dualGate n g :: dualList (n+1) gs

theorem dual_legal {b : Bool} {g : Gate} (hg : basic b g) (n : ℕ) : basic b (dualGate n g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨h,cap⟩ := hg
  change op = .and ∨ op = .or ∨ b = true ∧ op = .not at h
  change args.length ≤ 2 at cap
  rcases h with rfl|rfl|⟨rfl,rfl⟩
  · simp only [dualGate]; split <;> simp_all [basic]
  · exact ⟨.inl rfl,(List.length_filter_le ..).trans cap⟩
  · cases args with
    | nil => simp [basic, dualGate]
    | cons i tail => simp only [dualGate]; split <;> simp [basic]

theorem dual_step {b : Bool} (w : List Bool) (g : Gate) (hg : basic b g) :
    step (w.map Bool.not) (dualGate w.length g) = (step w g).map Bool.not := by
  have yes (i : ℕ) (hi : i < w.length) : (w.map Bool.not).getD i false = !(w.getD i false) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
  have no (i : ℕ) (hi : ¬i < w.length) : w.getD i false = false :=
    List.getD_eq_default _ _ (by omega)
  obtain ⟨op,args⟩ := g
  obtain ⟨h,cap⟩ := hg
  change op = .and ∨ op = .or ∨ b = true ∧ op = .not at h
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨k,tail⟩⟩⟩ <;> try simp at cap
  all_goals rcases h with rfl|rfl|⟨_,rfl⟩
  all_goals (try by_cases hi : i < w.length) <;> (try by_cases hj : j < w.length) <;>
    simp_all only [dualGate, step, List.map_cons, List.map_nil, List.map_append, List.all_cons,
      List.all_nil, List.filter_cons, List.filter_nil, GateOp.eval, List.any_cons,List.any_nil,
      List.headD_cons,List.headD_nil, decide_true,decide_false, Bool.true_and,Bool.false_and,
      Bool.and_true,Bool.and_false,Bool.or_true,Bool.or_false, Bool.false_or,Bool.true_or,
      Bool.false_eq_true,ite_true,ite_false, Bool.not_not,Bool.not_true,Bool.not_false,
      Bool.not_and,Bool.not_or, id_eq]
  all_goals (try rw [no i hi]) <;> (try rw [no j hj]) <;> simp

theorem dual_length (n : ℕ) (gs : List Gate) : (dualList n gs).length = gs.length := by
  induction gs generalizing n with | nil => rfl | cons g gs ih => simp [dualList,ih]

theorem dual_gates {b : Bool} (gs : List Gate) (hg : ∀ g ∈ gs, basic b g) (n : ℕ) :
    ∀ g ∈ dualList n gs, basic b g := by
  induction gs generalizing n with
  | nil => simp [dualList]
  | cons g gs ih =>
    simpa [dualList] using And.intro (dual_legal (hg g (by simp)) n)
      (ih (fun q hq => hg q (by simp [hq])) (n+1))

theorem dual_run {b : Bool} (gs : List Gate) (hg : ∀ g ∈ gs, basic b g) (w : List Bool) :
    (dualList w.length gs).foldl step (w.map Bool.not) = (gs.foldl step w).map Bool.not := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [dualList,List.foldl_cons,dual_step w g (hg g (by simp))]
    have len : (step w g).length = w.length+1 := by simp [step]
    rw [← len]
    exact ih (fun q hq => hg q (by simp [hq])) _

def realizesWith (P : List Gate → Prop) {n : ℕ} (b : Bool) (s : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), gs.length ≤ s ∧ (∀ g ∈ gs, basic b g) ∧ P gs ∧
    ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = f x

abbrev realizes {n : ℕ} (b : Bool) (s : ℕ) (f : (Fin n → Bool) → Bool) := realizesWith (fun _ => True) b s f

def dual {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) := !f (fun i => !(x i))

theorem realize_dual {P : List Gate → Prop} (closed : ∀ n gs, P gs → P (dualList n gs)) {n s : ℕ} {b : Bool} {f : (Fin n → Bool) → Bool}
    (pos : ∃ x, f x = true) (h : realizesWith P b s f) : realizesWith P b s (dual f) := by
  obtain ⟨gs,o,sz,hg,hP,he⟩ := h
  have valid : o < n+gs.length := by
    obtain ⟨x,hx⟩ := pos
    by_contra! hout
    have len := run_length gs (List.ofFn x)
    simp only [List.length_ofFn] at len
    have ev := he x
    change (gs.foldl step (List.ofFn x)).getD o false = f x at ev
    rw [List.getD_eq_default _ _ (by omega), hx] at ev
    contradiction
  refine ⟨dualList n gs,o,(dual_length ..).trans_le sz,dual_gates gs hg n,closed n gs hP,?_⟩
  intro x
  let y (i : Fin n) := !(x i)
  let w := List.ofFn y
  have len : w.length = n := List.length_ofFn
  have xm : List.ofFn x = w.map Bool.not := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp [Function.comp_def,y]
  change ((dualList n gs).foldl step (List.ofFn x)).getD o false = !f y
  rw [xm,← len,dual_run gs hg w]
  have inh : o < (gs.foldl step w).length := by rw [run_length,len]; exact valid
  have ev := he y
  change (gs.foldl step w).getD o false = f y at ev
  rw [← ev]
  simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem inh]


def renumber {n : ℕ} (p : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  if h : i < n then (p ⟨i,h⟩).val else i

def renameGate {n : ℕ} (p : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (renumber p)⟩

theorem rename_read {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Fin n → Bool) (suffix : List Bool) (i : ℕ) :
    (List.ofFn x ++ suffix).getD (renumber p i) false =
      (List.ofFn (x ∘ p) ++ suffix).getD i false := by
  by_cases h : i < n
  · simp only [renumber, dif_pos h]
    rw [List.getD_append _ _ _ _ (by simpa using (p ⟨i,h⟩).isLt),
        List.getD_append _ _ _ _ (by simpa using h)]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using (p ⟨i,h⟩).isLt : (p ⟨i,h⟩).val < (List.ofFn x).length),
      List.getElem?_eq_getElem (by simpa using h : i < (List.ofFn (x ∘ p)).length), Option.getD_some,List.getElem_ofFn, Function.comp_apply]
  · simp only [renumber, dif_neg h]
    rw [List.getD_append_right _ _ _ _ (by simp; omega),List.getD_append_right _ _ _ _ (by simp; omega)]
    simp

theorem rename_run {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Fin n → Bool) (gs : List Gate)
    (suffix : List Bool) : ∃ t : List Bool,
    ((gs.map (renameGate p)).foldl step (List.ofFn x ++ suffix) = List.ofFn x ++ t) ∧
    (gs.foldl step (List.ofFn (x ∘ p) ++ suffix) = List.ofFn (x ∘ p) ++ t) := by
  induction gs generalizing suffix with
  | nil => exact ⟨suffix,rfl,rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map (fun i => (List.ofFn (x ∘ p) ++ suffix).getD i false))
    have a : step (List.ofFn x ++ suffix) (renameGate p g) = List.ofFn x ++ (suffix ++ [v]) := by
      have reads : ((renameGate p g).inputs.map ((List.ofFn x ++ suffix).getD · false)) =
          g.inputs.map ((List.ofFn (x ∘ p) ++ suffix).getD · false) := by
        change (g.inputs.map _).map _ = _
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact rename_read p x suffix i
      simp only [step,reads,List.append_assoc]
      rfl
    have orig : step (List.ofFn (x ∘ p) ++ suffix) g = List.ofFn (x ∘ p) ++ (suffix ++ [v]) := List.append_assoc ..
    simp only [List.map_cons,List.foldl_cons,a,orig]
    exact ih (suffix ++ [v])

def permute {n : ℕ} (p : Equiv.Perm (Fin n)) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) := f (x ∘ p)

theorem realize_permute {P : List Gate → Prop} {n s : ℕ} {b : Bool} {f : (Fin n → Bool) → Bool}
    (p : Equiv.Perm (Fin n)) (closed : ∀ gs, P gs → P (gs.map (renameGate p))) (h : realizesWith P b s f) : realizesWith P b s (permute p f) := by
  obtain ⟨gs,o,cap,hg,hP,he⟩ := h
  refine ⟨gs.map (renameGate p),renumber p o,by simpa using cap,?_,closed gs hP,?_⟩
  · intro gate mem
    obtain ⟨g,hg',rfl⟩ := List.mem_map.mp mem
    simpa [basic,renameGate] using hg g hg'
  · intro x
    obtain ⟨t,ht,ht'⟩ := rename_run p x gs []
    simp only [List.append_nil] at ht ht'
    change ((gs.map (renameGate p)).foldl step (List.ofFn x)).getD (renumber p o) false = f (x ∘ p)
    rw [ht, rename_read, ← ht']
    exact he (x ∘ p)

theorem permute_iff_with {P : List Gate → Prop} {n s : ℕ} {b : Bool} {f : (Fin n → Bool) → Bool}
    (closed : ∀ (q : Equiv.Perm (Fin n)) gs, P gs → P (gs.map (renameGate q)))
    (p : Equiv.Perm (Fin n)) : realizesWith P b s (permute p f) ↔ realizesWith P b s f := by
  refine ⟨fun h => ?_, realize_permute p (closed p)⟩
  have eq : permute p.symm (permute p f) = f := by
    funext x
    change f _ = f x
    congr 1
    funext i
    exact congrArg x (p.symm_apply_apply i)
  exact eq ▸ realize_permute p.symm (closed _) h

theorem dual_iff_with {P : List Gate → Prop} (closed : ∀ n gs, P gs → P (dualList n gs)) {n s : ℕ} {b : Bool} {f : (Fin n → Bool) → Bool}
    (pos : ∃ x, f x = true) (neg : ∃ x, f x = false) : realizesWith P b s (dual f) ↔ realizesWith P b s f := by
  refine ⟨fun h => ?_,realize_dual closed pos⟩
  obtain ⟨x,hx⟩ := neg
  have hp : ∃ y, dual f y = true := ⟨fun i => !(x i), by simp [dual,hx]⟩
  have eq : dual (dual f) = f := by funext z; simp [dual]
  exact eq ▸ realize_dual closed hp h

theorem permute_iff {n s : ℕ} {b : Bool} {f : (Fin n → Bool) → Bool} (p : Equiv.Perm (Fin n)) :
    realizes b s (permute p f) ↔ realizes b s f := permute_iff_with (fun _ _ h => h) p

theorem dual_iff {n s : ℕ} {b : Bool} {f : (Fin n → Bool) → Bool}
    (pos : ∃ x, f x = true) (neg : ∃ x, f x = false) :
    realizes b s (dual f) ↔ realizes b s f := dual_iff_with (fun _ _ h => h) pos neg

end CircuitSymmetry
