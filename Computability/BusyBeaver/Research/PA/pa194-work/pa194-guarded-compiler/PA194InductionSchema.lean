import PA194NameFactsProof
import PA194InductionForms
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The translated induction axiom from ordinal induction in the source theory

`induction_body`: for every internal formula `p` of arity one of the arithmetic language,
possibly nonstandard and with parameters, the source theory derives, under the domain guards,
the translation of `p[0] → (∀x (p → p[S x]) → ∀x p)`. The inputs are the term facts, the
twelve fixed source facts, and ordinal induction of the source theory for every internal
property (`indCode`).

The argument is one more instance of the schematic method. With the letters `Q` for the
translation of `p` and `QS` for that of `p[S x]`, the sentence

  induction for `Q` → (names of zero satisfy `Q`) → (`QS x` implies that names of the
  successor of `x` satisfy `Q`) → `∀x (Q x → QS x)` → `∀x Q x`

holds in every structure with the fixed hypotheses. Its second and third premises are the
universally closed Leibniz lemma at the terms `0` and `S(&0)`.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher PA194Schematic

/-! ### The sentence -/

/-- The letter for the translation of `p`. -/
def sQ {n : ℕ} (t : ST n) : SF n := sAt (sLet 0) t
/-- The letter for the translation of `p[S x]`. -/
def sQS {n : ℕ} (t : ST n) : SF n := sAt (sLet 1) t
def sIndBase : SF 0 := ∀⁰ (∼(sDom #0 ⋏ sZero #0) ⋎ sQ #0)
def sIndStep : SF 0 := ∀⁰ ∀⁰ (∼(sDom #1 ⋏ (sDom #0 ⋏ (sSucc #1 #0 ⋏ sQ #1))) ⋎ sQ #0)
def sIndConcl : SF 0 := ∀⁰ (∼(sDom #0) ⋎ sQ #0)
/-- Ordinal induction for `Q`, in the shape of the source theory's statement. -/
def sInd : SF 0 := ∼sIndBase ⋎ (∼sIndStep ⋎ sIndConcl)
/-- Every name of zero satisfies `Q`. -/
def sHbase : SF 0 := ∀⁰ (∼(sDom #0) ⋎ (∼(sNameAtom sZeroV) ⋎ sQ #0))
/-- `y` is a name of the successor of `x`; `x` is `#1` and `y` is `#0`. -/
def sSuccName : SF 2 :=
  sEqForm (n := 2) (sVarV #1 #2) (sDom #0 ⋏ (∃⁰ ((sDom #0 ⋏ sEq #0 #4) ⋏ sSucc #0 #1)))
/-- If `QS x`, every name of the successor of `x` satisfies `Q`. -/
def sHstep : SF 0 :=
  ∀⁰ (∼(sDom #0) ⋎ (∼(sQS #0) ⋎ (∀⁰ (∼(sDom #0) ⋎ (∼sSuccName ⋎ sQ #0)))))
def sX2 : SF 0 := ∀⁰ (∼(sDom #0) ⋎ (∼(sQ #0) ⋎ sQS #0))
def fInd : SF 0 := sInd 🡒 sHbase 🡒 sHstep 🡒 sX2 🡒 sIndConcl

section semantics
variable {M : Type} [s : Structure NL M]

def mSuccName (x y : M) : Prop :=
  ∃ v w : M, mVarV v y ∧ (mD w ∧ ∃ u : M, mVarV u x ∧ mS u w) ∧ mI v w

@[simp] theorem ev_sQ {n : ℕ} (b : Fin n → M) (t : ST n) : ev b (sQ t) ↔ mL 0 (tv b t) := by
  simp [sQ]
@[simp] theorem ev_sQS {n : ℕ} (b : Fin n → M) (t : ST n) : ev b (sQS t) ↔ mL 1 (tv b t) := by
  simp [sQS]
theorem ev_sIndBase : ev (![] : Fin 0 → M) sIndBase ↔ ∀ z : M, ¬(mD z ∧ mZ z) ∨ mL 0 z := by
  simp [sIndBase]
  exact forall_congr' fun x => by tauto
theorem ev_sIndStep : ev (![] : Fin 0 → M) sIndStep ↔
    ∀ x y : M, ¬(mD x ∧ (mD y ∧ (mS x y ∧ mL 0 x))) ∨ mL 0 y := by
  simp [sIndStep]
  exact forall_congr' fun x => forall_congr' fun y => by tauto
theorem ev_sIndConcl : ev (![] : Fin 0 → M) sIndConcl ↔ ∀ x : M, ¬mD x ∨ mL 0 x := by
  simp [sIndConcl]
theorem ev_sHbase : ev (![] : Fin 0 → M) sHbase ↔
    ∀ y : M, ¬mD y ∨ (¬mName mZeroV y ∨ mL 0 y) := by
  have h : ∀ x : M, ev ![x] (sNameAtom sZeroV) ↔ mName mZeroV x := fun x => by
    have h1 := wOf_sNameAtom sZeroV x
    rw [wOf_sZeroV'] at h1
    exact h1
  simp [sHbase, h]
theorem ev_sSuccName (x y : M) : ev ![y, x] sSuccName ↔ mSuccName x y := by
  simp [sSuccName, sEqForm, sVarV, mSuccName, mVarV]
theorem ev_sHstep : ev (![] : Fin 0 → M) sHstep ↔
    ∀ x : M, ¬mD x ∨ (¬mL 1 x ∨ ∀ y : M, ¬mD y ∨ (¬mSuccName x y ∨ mL 0 y)) := by
  have h : ∀ x y : M, ev ![y, x] sSuccName ↔ mSuccName x y := ev_sSuccName
  simp [sHstep, h]
theorem ev_sX2 : ev (![] : Fin 0 → M) sX2 ↔ ∀ x : M, ¬mD x ∨ (¬mL 0 x ∨ mL 1 x) := by
  simp [sX2]

theorem ev_sInd : ev (![] : Fin 0 → M) sInd ↔
    (¬(∀ z : M, ¬(mD z ∧ mZ z) ∨ mL 0 z) ∨
      (¬(∀ x y : M, ¬(mD x ∧ (mD y ∧ (mS x y ∧ mL 0 x))) ∨ mL 0 y) ∨
        ∀ x : M, ¬mD x ∨ mL 0 x)) := by
  simp only [sInd, LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg,
    LogicalConnective.Prop.or_eq, LogicalConnective.Prop.neg_eq, ev_sIndBase, ev_sIndStep,
    ev_sIndConcl]

theorem m_ind (H : MTheta M) {Q QS : M → Prop}
    (hI : ¬(∀ z : M, ¬(mD z ∧ mZ z) ∨ Q z) ∨
      (¬(∀ x y : M, ¬(mD x ∧ (mD y ∧ (mS x y ∧ Q x))) ∨ Q y) ∨ ∀ x : M, ¬mD x ∨ Q x))
    (hB : ∀ y : M, ¬mD y ∨ (¬mName mZeroV y ∨ Q y))
    (hS : ∀ x : M, ¬mD x ∨ (¬QS x ∨ ∀ y : M, ¬mD y ∨ (¬mSuccName x y ∨ Q y)))
    (hX : ∀ x : M, ¬mD x ∨ (¬Q x ∨ QS x)) : ∀ x : M, ¬mD x ∨ Q x := by
  have base : ∀ z : M, ¬(mD z ∧ mZ z) ∨ Q z := fun z => not_or_of_imp fun hz =>
    ((hB z).resolve_left (fun hn => hn hz.1)).resolve_left
      (fun hn => hn (m_selfName H hz.1 ⟨hz.1, hz.2⟩))
  have step : ∀ x y : M, ¬(mD x ∧ (mD y ∧ (mS x y ∧ Q x))) ∨ Q y := fun x y =>
    not_or_of_imp fun h => by
      obtain ⟨dx, dy, sxy, qx⟩ := h
      have qs : QS x := ((hX x).resolve_left (fun hn => hn dx)).resolve_left (fun hn => hn qx)
      have h1 := ((hS x).resolve_left (fun hn => hn dx)).resolve_left (fun hn => hn qs)
      exact ((h1 y).resolve_left (fun hn => hn dy)).resolve_left (fun hn => hn
        ⟨y, y, ⟨dy, H.e1 y⟩, ⟨dy, x, ⟨dx, H.e1 x⟩, sxy⟩, H.ei y y y dy dy (H.e1 y) (H.e1 y)⟩)
  exact (hI.resolve_left (fun hn => hn base)).resolve_left (fun hn => hn step)

theorem valid_ind (M : Type) [Nonempty M] [s : Structure NL M] : M↓[NL] ⊧ sWith fInd := by
  show ev (![] : Fin 0 → M) (sWith fInd)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fInd, ev_imp]
  intro hI hB hS hX
  exact ev_sIndConcl.mpr (m_ind H (ev_sInd.mp hI) (ev_sHbase.mp hB) (ev_sHstep.mp hS)
    (ev_sX2.mp hX))

end semantics

section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Typed atoms under shift -/

@[simp] theorem tDom_shift {n : ℕ} (t : Bootstrapping.Semiterm V SourceL n) :
    (tDom t).shift = tDom t.shift := by
  apply Bootstrapping.Semiformula.ext
  simp only [Bootstrapping.Semiformula.val_shift, tDom_val]
  rw [domainCode_shift t.isSemiterm]
  rfl
@[simp] theorem tEq_shift {n : ℕ} (t u : Bootstrapping.Semiterm V SourceL n) :
    (tEq t u).shift = tEq t.shift u.shift := by
  apply Bootstrapping.Semiformula.ext
  simp only [Bootstrapping.Semiformula.val_shift, tEq_val]
  rw [equalityCode_shift t.isSemiterm u.isSemiterm]
  rfl
@[simp] theorem tIso_shift {n : ℕ} (t u : Bootstrapping.Semiterm V SourceL n) :
    (tIso t u).shift = tIso t.shift u.shift := by
  apply Bootstrapping.Semiformula.ext
  simp only [Bootstrapping.Semiformula.val_shift, tIso_val]
  rw [orderIsoCode_shift t.isSemiterm u.isSemiterm]
  rfl
@[simp] theorem tSucc_shift {n : ℕ} (t u : Bootstrapping.Semiterm V SourceL n) :
    (tSucc t u).shift = tSucc t.shift u.shift := by
  apply Bootstrapping.Semiformula.ext
  simp only [Bootstrapping.Semiformula.val_shift, tSucc_val]
  rw [successorCode_shift t.isSemiterm u.isSemiterm]
  rfl
@[simp] theorem tSucc_subst {n m : ℕ} (t u : Bootstrapping.Semiterm V SourceL n)
    (w : Bootstrapping.SemitermVec V SourceL n m) :
    (tSucc t u).subst w = tSucc (t.subst w) (u.subst w) := by
  unfold tSucc
  rw [Bootstrapping.Semiformula.substs_substs]
  simp

/-! ### The codes of the instances -/

/-- Ordinal induction of the source theory for the property `q`:
`¬base ∨ (¬step ∨ conclusion)`. -/
noncomputable def indCode (q : V) : V :=
  neg SourceL (^∀ (neg SourceL (domainCode (^#(0 : V)) ^⋏ zeroCode (^#(0 : V))) ^⋎ q)) ^⋎
    (neg SourceL (^∀ (^∀ (neg SourceL (domainCode (^#(1 : V)) ^⋏ (domainCode (^#(0 : V)) ^⋏
        (successorCode (^#(1 : V)) (^#(0 : V)) ^⋏ substs1 SourceL (^#(1 : V)) q))) ^⋎ q))) ^⋎
      ^∀ (neg SourceL (domainCode (^#(0 : V))) ^⋎ q))

theorem subst_bvar0_self {q : V} (hq : IsSemiformula SourceL 1 q) :
    subst SourceL (?[^#(0 : V)] : V) q = q :=
  subst_eq_self hq (by simp) (fun i hi => by
    have h0 : i = 0 := by simpa using hi
    subst h0
    simp)

section codes
variable (A : Fin 4 → Bootstrapping.Semiformula V SourceL 1)

theorem v_ind : (instS (sig A) sInd).val = indCode (A 0).val := by
  have e := subst_bvar0_self (show IsSemiformula SourceL 1 (A 0).val by simp)
  simp only [sInd, sIndBase, sIndStep, sIndConcl, instS_or, instS_neg, instS_all, instS_and,
    Bootstrapping.Semiformula.val_or, Bootstrapping.Semiformula.val_neg,
    Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_and]
  simp [sQ, indCode, substs1, e]
theorem v_concl : (instS (sig A) sIndConcl).val = ^∀ (guardBody ^⋎ (A 0).val) := by
  simp [sIndConcl, sQ, guardBody]
theorem v_x2 : (instS (sig A) sX2).val =
    ^∀ (guardBody ^⋎ (neg SourceL (A 0).val ^⋎ (A 1).val)) := by
  simp [sX2, sQ, sQS, guardBody]
theorem v_hbase : (instS (sig A) sHbase).val = ^∀ (guardBody ^⋎
    (neg SourceL (eqForm (variableValue (^#(1 : V)) (^#(2 : V)))
      (substs1 SourceL (^#(0 : V)) (valBody (zeroT : V)))) ^⋎ (A 0).val)) := by
  simp [sHbase, sQ, guardBody, tNameAtom_val, tZeroV_val]

/-- `y` is a name of the successor of `x`, typed. -/
noncomputable def tSuccName : Bootstrapping.Semiformula V SourceL 2 :=
  tEqForm (n := 2) (tVarV (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 2))
    (tDom (Bootstrapping.Semiterm.bvar 0) ⋏ (∃⁰ ((tDom (Bootstrapping.Semiterm.bvar 0) ⋏
      tEq (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 4)) ⋏
      tSucc (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1))))
/-- The matrix of the step hypothesis. -/
noncomputable def tXs (Q QS : Bootstrapping.Semiformula V SourceL 1) :
    Bootstrapping.Semiformula V SourceL 1 :=
  ∼QS ⋎ (∀⁰ (∼(tDom (Bootstrapping.Semiterm.bvar 0)) ⋎
    (∼(tSuccName : Bootstrapping.Semiformula V SourceL 2) ⋎
      Q.subst ![Bootstrapping.Semiterm.bvar 0])))

theorem instS_sSuccName : instS (sig A) sSuccName = tSuccName := by
  simp [sSuccName, tSuccName]
theorem instS_sHstep :
    instS (sig A) sHstep = ∀⁰ (∼(tDom (Bootstrapping.Semiterm.bvar 0)) ⋎ tXs (A 0) (A 1)) := by
  simp [sHstep, tXs, sQ, sQS, instS_sSuccName]
end codes

/-- Opening the matrix of the step hypothesis at the variable `&0`. -/
theorem tXs_free (Q QS : Bootstrapping.Semiformula V SourceL 1) :
    (tXs Q QS).free = ∼QS.free ⋎ (∀⁰ (∼(tDom (Bootstrapping.Semiterm.bvar 0)) ⋎
      (∼(tNameAtom (tSuccV (tBox (tEq (Bootstrapping.Semiterm.bvar 0)
        (Bootstrapping.Semiterm.fvar 0))))) ⋎ Q.shift))) := by
  simp [tXs, tSuccName, tNameAtom, tSuccV, tBox, tEqForm, tVarV, Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs,
    Bootstrapping.SemitermVec.q]

/-! ### The derivation -/

variable {T : Theory SourceL} [T.Δ₁]

theorem exTF {q : V} (hq : IsSemiformula SourceL 1 q) :
    ∃ Q : Bootstrapping.Semiformula V SourceL 1, Q.val = q :=
  ⟨⟨q, by simpa using hq⟩, rfl⟩

/-- The step hypothesis: for every member `x` of the domain, if the translation of `p[S x]`
holds then every name of the successor of `x` satisfies the translation of `p`. It is the
universally closed Leibniz lemma at the term `S(&0)`, generalized over `&0`. -/
theorem step_derivable (F : TermFacts (V := V) T) {p : V}
    (hp : IsSemiformula PA194PAeq.language 1 p) {Q QS : Bootstrapping.Semiformula V SourceL 1}
    (hQ : Q.val = trBody p) (hQS : QS.val = trBody (substs1 PA194PAeq.language succVar p)) :
    GDerivable T (insert (^∀ (guardBody ^⋎ (tXs Q QS).val)) (∅ : V)) := by
  have hpS := substs1_succVar_valid hp
  have hc : IsSemiterm PA194PAeq.language 0 (^&(0 : V)) := by simp
  have hst : IsSemiterm PA194PAeq.language 0 (succT (^&(0 : V))) := succT_valid hc
  have hXs : IsSemiformula SourceL 1 (tXs Q QS).val := by simp
  have hall : IsFormula SourceL (^∀ (guardBody ^⋎ (tXs Q QS).val)) :=
    IsSemiformula.all.mpr (by simpa using IsSemiformula.or.mpr ⟨guardBody_valid (V := V),hXs⟩)
  have e1 : QS.free.val = tr (substs1 PA194PAeq.language (succT (^&(0 : V)))
      (shift PA194PAeq.language p)) := by
    rw [Bootstrapping.Semiformula.free_val, hQS, ← tr_free hpS, free_substs1_succVar hp]
  have e2 : (∀⁰ (∼(tDom (Bootstrapping.Semiterm.bvar 0)) ⋎
      (∼(tNameAtom (tSuccV (tBox (tEq (Bootstrapping.Semiterm.bvar 0)
        (Bootstrapping.Semiterm.fvar 0))))) ⋎ Q.shift)) :
      Bootstrapping.Semiformula V SourceL 0).val =
      tr (allNames (succT (^&(0 : V))) (shift PA194PAeq.language p)) := by
    rw [tr_allNames hst hp.shift, trBody_shift hp, ← hQ, ← tSuccV_val hc (boxVar (0 : V))]
    simp [guardBody, tNameAtom_val]
  have efree : free SourceL (tXs Q QS).val =
      neg SourceL (tr (substs1 PA194PAeq.language (succT (^&(0 : V)))
        (shift PA194PAeq.language p))) ^⋎
      tr (allNames (succT (^&(0 : V))) (shift PA194PAeq.language p)) := by
    rw [← Bootstrapping.Semiformula.free_val, tXs_free]
    simp only [Bootstrapping.Semiformula.val_or, Bootstrapping.Semiformula.val_neg]
    rw [e1, e2]
  have hn : IsFormula SourceL (neg SourceL (tr (substs1 PA194PAeq.language (succT (^&(0 : V)))
      (shift PA194PAeq.language p)))) :=
    IsSemiformula.neg_iff.mpr (tr_valid (IsSemiformula.substs1 hst hp.shift))
  have ha : IsFormula SourceL (tr (allNames (succT (^&(0 : V))) (shift PA194PAeq.language p))) :=
    tr_valid (allNames_valid hst hp.shift)
  refine GDerivable.all_rel hXs (by simp) ?_
  rw [mem_setShift_insert, setShift_empty, efree]
  refine GDerivable.or_m
    (p := neg SourceL (tr (substs1 PA194PAeq.language (succT (^&(0 : V)))
      (shift PA194PAeq.language p))))
    (q := tr (allNames (succT (^&(0 : V))) (shift PA194PAeq.language p))) (by simp) ?_
  exact GDerivable.wk (fs_cons hn (fs_cons ha (fs_cons (IsSemiformula.or.mpr ⟨hn,ha⟩)
    (fs_cons hall.shift fs_nil)))) (by set_tac) (leibnizAll F hp.shift hst)

/-- Two cuts and two disjunction introductions. -/
theorem assemble {P0 HB HS X2 C : V}
    (g : GDerivable T (insert (neg SourceL HB) (insert (neg SourceL HS)
      (insert (neg SourceL X2) (insert C (∅ : V))))))
    (gs : GDerivable T (insert HS (∅ : V)))
    (gb : GDerivable T (insert (neg SourceL P0) (insert HB (∅ : V)))) :
    GDerivable T (insert (neg SourceL P0 ^⋎ (neg SourceL X2 ^⋎ C)) (∅ : V)) := by
  have hg := g.isFormulaSet
  have fnHB := (IsFormulaSet.insert_iff.mp hg).1
  have h1 := (IsFormulaSet.insert_iff.mp hg).2
  have h2 := (IsFormulaSet.insert_iff.mp h1).2
  have fnX2 := (IsFormulaSet.insert_iff.mp h2).1
  have fC := (IsFormulaSet.insert_iff.mp (IsFormulaSet.insert_iff.mp h2).2).1
  have fHS := (IsFormulaSet.insert_iff.mp gs.isFormulaSet).1
  have hb := gb.isFormulaSet
  have fnP0 := (IsFormulaSet.insert_iff.mp hb).1
  have fHB := (IsFormulaSet.insert_iff.mp (IsFormulaSet.insert_iff.mp hb).2).1
  have f1 : IsFormula SourceL (neg SourceL X2 ^⋎ C) := IsSemiformula.or.mpr ⟨fnX2,fC⟩
  have f2 : IsFormula SourceL (neg SourceL P0 ^⋎ (neg SourceL X2 ^⋎ C)) :=
    IsSemiformula.or.mpr ⟨fnP0,f1⟩
  refine GDerivable.or_m (p := neg SourceL P0) (q := neg SourceL X2 ^⋎ C) (by simp) ?_
  refine GDerivable.or_m (p := neg SourceL X2) (q := C) (by simp) ?_
  have hΔ : IsFormulaSet SourceL (insert (neg SourceL X2) (insert C (insert (neg SourceL P0)
      (insert (neg SourceL X2 ^⋎ C)
        (insert (neg SourceL P0 ^⋎ (neg SourceL X2 ^⋎ C)) (∅ : V)))))) :=
    fs_cons fnX2 (fs_cons fC (fs_cons fnP0 (fs_cons f1 (fs_cons f2 fs_nil))))
  have inner : GDerivable T (insert (neg SourceL HB) (insert (neg SourceL X2) (insert C
      (insert (neg SourceL P0) (insert (neg SourceL X2 ^⋎ C)
        (insert (neg SourceL P0 ^⋎ (neg SourceL X2 ^⋎ C)) (∅ : V))))))) :=
    GDerivable.cut_wk (fs_cons fnHB hΔ) fHS gs g (by set_tac) (by set_tac)
  exact GDerivable.cut_wk hΔ fHB gb inner (by set_tac) (by set_tac)

/-- The translated induction axiom for an arbitrary internal formula, before the closure of
its parameters. -/
theorem induction_body (F : TermFacts (V := V) T) (S : SourceFacts (V := V) T)
    (hInd : ∀ q : V, IsSemiformula SourceL 1 q → Provable T (indCode q)) {p : V}
    (hp : IsSemiformula PA194PAeq.language 1 p) :
    GDerivable T (insert (tr (indBody p)) (∅ : V)) := by
  have hpS := substs1_succVar_valid hp
  obtain ⟨Q, hQ⟩ := exTF (trBody_valid hp)
  obtain ⟨QS, hQS⟩ := exTF (trBody_valid hpS)
  obtain ⟨A, a0, a1, -, -⟩ := exA4 Q QS ⊤ ⊤
  have h := with_facts A S fInd valid_ind
  simp only [fInd, instS_imp] at h
  have hI : T.internalize V ⊢ instS (sig A) sInd :=
    (TProvable.iff_provable (T := T.internalize V) (σ := instS (sig A) sInd)).mpr (by
      rw [v_ind, a0, hQ]
      exact hInd _ (trBody_valid hp))
  have g := gd3 (tmp h hI)
  have eHb : (instS (sig A) sHbase).val = tr (allNames (zeroT : V) p) := by
    rw [v_hbase, a0, hQ, tr_allNames zeroT_valid hp]
  have eX2 : (instS (sig A) sX2).val = ^∀ (guardBody ^⋎ (neg SourceL (trBody p) ^⋎
      trBody (substs1 PA194PAeq.language succVar p))) := by
    rw [v_x2, a0, a1, hQ, hQS]
  have eC : (instS (sig A) sIndConcl).val = ^∀ (guardBody ^⋎ trBody p) := by
    rw [v_concl, a0, hQ]
  have eHs : (instS (sig A) sHstep).val = ^∀ (guardBody ^⋎ (tXs Q QS).val) := by
    rw [instS_sHstep, a0, a1]
    simp [guardBody]
  rw [eHb, eHs, eX2, eC] at g
  rw [tr_indBody hp]
  exact assemble g (step_derivable F hp hQ hQS) (leibnizAll F hp zeroT_valid)

#print axioms step_derivable
#print axioms assemble
#print axioms induction_body
#print axioms v_ind
#print axioms v_hbase
#print axioms instS_sHstep
#print axioms tXs_free
end generic

#print axioms m_ind
#print axioms valid_ind
end PA194GuardedCompiler
