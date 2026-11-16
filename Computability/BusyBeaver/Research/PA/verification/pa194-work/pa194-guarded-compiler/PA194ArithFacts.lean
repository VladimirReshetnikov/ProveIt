import PA194NameFactsProof
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# Congruence of addition and multiplication, and the two successor laws

Guarded derivations of the translations of four open formulas of the arithmetic language:

* `cong_add`, `cong_mul`: `s₁ = s₁' → s₂ = s₂' → s₁ + s₂ = s₁' + s₂'` and the same for `·`,
  for arbitrary internal terms, from `SourceFacts T`;
* `addSucc_open`: `S(&a) + &b = S(&a + &b)`, from `SourceFacts T` and one more fixed fact
  about the source theory (`sA3`);
* `mulSucc_open`: `S(&a) · &b = &b + &a · &b`, from `SourceFacts T` and `sM3`.

They are the matrices of the four fixed axioms of the arithmetic theory that concern
addition and multiplication beyond their value at zero. Each is an instance of a sentence
over the letters of `PA194NameSchema`; the variables are handled by letters "equal to `&a`",
whose value formulas are inhabited under the domain guard of the variable.
-/
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher PA194Schematic

/-! ### The sentences -/

def fCAdd : SF 0 :=
  sEqVal (sBox 0) (sBox 1) 🡒 sEqVal (sBox 2) (sBox 3) 🡒
    sEqVal (sAddV (sBox 0) (sBox 2)) (sAddV (sBox 1) (sBox 3))
def fCMul : SF 0 :=
  sEqVal (sBox 0) (sBox 1) 🡒 sEqVal (sBox 2) (sBox 3) 🡒
    sEqVal (sMulV (sBox 0) (sBox 2)) (sMulV (sBox 1) (sBox 3))
/-- The `i`-th value formula has a member. -/
def sNE (i : Fin 4) : SF 0 := ∃⁰ (sDom #0 ⋏ sAt (sLet i) #0)
/-- The sum with a successor on the left: if `u'` is a successor of `u`, `w` a sum of `u'`
and `v`, `w₀` a sum of `u` and `v`, and `w₁` a successor of `w₀`, then `w` and `w₁` are
isomorphic. The variables are `u, u', v, w, w₀, w₁ = #5, …, #0`. -/
def sA3 : SF 0 :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ (sDom #5 🡒 sDom #4 🡒 sDom #3 🡒 sDom #2 🡒 sDom #1 🡒 sDom #0 🡒
    sSucc #5 #4 🡒 sAdd #4 #3 #2 🡒 sAdd #5 #3 #1 🡒 sSucc #1 #0 🡒 sIso #2 #0)
/-- The product with a successor on the left: if `u'` is a successor of `u`, `w` a product
of `u'` and `v`, `w₀` a product of `u` and `v`, and `w₁` a sum of `v` and `w₀`, then `w` and
`w₁` are isomorphic. -/
def sM3 : SF 0 :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ ∀⁰ (sDom #5 🡒 sDom #4 🡒 sDom #3 🡒 sDom #2 🡒 sDom #1 🡒 sDom #0 🡒
    sSucc #5 #4 🡒 sMul #4 #3 #2 🡒 sMul #5 #3 #1 🡒 sAdd #3 #1 #0 🡒 sIso #2 #0)
def fAddSucc : SF 0 :=
  sA3 🡒 sNE 0 🡒 sNE 1 🡒
    sEqVal (sAddV (sSuccV (sBox 0)) (sBox 1)) (sSuccV (sAddV (sBox 0) (sBox 1)))
def fMulSucc : SF 0 :=
  sM3 🡒 sNE 0 🡒 sNE 1 🡒
    sEqVal (sMulV (sSuccV (sBox 1)) (sBox 0)) (sAddV (sBox 0) (sMulV (sBox 1) (sBox 0)))

section semantics
variable {M : Type} [s : Structure NL M]

theorem ev_sNE (i : Fin 4) : ev (![] : Fin 0 → M) (sNE i) ↔ ∃ v : M, wOf (sBox i) v := by
  have h : ∀ x : M, ev ![x] (sLet i) ↔ mL i x := wOf_sLet i
  simp [sNE, wOf, sBox, h]
theorem ev_sA3 : ev (![] : Fin 0 → M) sA3 ↔
    ∀ u u' v w w0 w1 : M, mD u → mD u' → mD v → mD w → mD w0 → mD w1 →
      mS u u' → mA u' v w → mA u v w0 → mS w0 w1 → mI w w1 := by
  simp [sA3]
theorem ev_sM3 : ev (![] : Fin 0 → M) sM3 ↔
    ∀ u u' v w w0 w1 : M, mD u → mD u' → mD v → mD w → mD w0 → mD w1 →
      mS u u' → mMu u' v w → mMu u v w0 → mA v w0 w1 → mI w w1 := by
  simp [sM3]

theorem m_cAdd (H : MTheta M) {P0 P1 P2 P3 : M → Prop} (h0 : ∀ x, P0 x → mD x)
    (h1 : ∀ x, P1 x → mD x) (h2 : ∀ x, P2 x → mD x) (h3 : ∀ x, P3 x → mD x)
    (e : mEqVal P0 P1) (e' : mEqVal P2 P3) : mEqVal (mAddV P0 P2) (mAddV P1 P3) := by
  obtain ⟨v, w, pv, pw, ivw⟩ := e
  obtain ⟨v', w', pv', pw', ivw'⟩ := e'
  obtain ⟨z, dz, az⟩ := H.a1 v v' (h0 v pv) (h2 v' pv')
  obtain ⟨z', dz', az'⟩ := H.a1 w w' (h1 w pw) (h3 w' pw')
  exact ⟨z, z', ⟨dz, v, v', pv, pv', az⟩, ⟨dz', w, w', pw, pw', az'⟩,
    H.a2 v v' z w w' z' (h0 v pv) (h2 v' pv') dz (h1 w pw) (h3 w' pw') dz' az az' ivw ivw'⟩

theorem m_cMul (H : MTheta M) {P0 P1 P2 P3 : M → Prop} (h0 : ∀ x, P0 x → mD x)
    (h1 : ∀ x, P1 x → mD x) (h2 : ∀ x, P2 x → mD x) (h3 : ∀ x, P3 x → mD x)
    (e : mEqVal P0 P1) (e' : mEqVal P2 P3) : mEqVal (mMulV P0 P2) (mMulV P1 P3) := by
  obtain ⟨v, w, pv, pw, ivw⟩ := e
  obtain ⟨v', w', pv', pw', ivw'⟩ := e'
  obtain ⟨z, dz, az⟩ := H.m1 v v' (h0 v pv) (h2 v' pv')
  obtain ⟨z', dz', az'⟩ := H.m1 w w' (h1 w pw) (h3 w' pw')
  exact ⟨z, z', ⟨dz, v, v', pv, pv', az⟩, ⟨dz', w, w', pw, pw', az'⟩,
    H.m2 v v' z w w' z' (h0 v pv) (h2 v' pv') dz (h1 w pw) (h3 w' pw') dz' az az' ivw ivw'⟩

theorem m_addSucc (H : MTheta M)
    (H3 : ∀ u u' v w w0 w1 : M, mD u → mD u' → mD v → mD w → mD w0 → mD w1 →
      mS u u' → mA u' v w → mA u v w0 → mS w0 w1 → mI w w1)
    {X Y : M → Prop} (hX : ∀ x, X x → mD x) (hY : ∀ x, Y x → mD x)
    (nX : ∃ v : M, X v) (nY : ∃ v : M, Y v) :
    mEqVal (mAddV (mSuccV X) Y) (mSuccV (mAddV X Y)) := by
  obtain ⟨x, px⟩ := nX
  obtain ⟨y, py⟩ := nY
  have dx := hX x px
  have dy := hY y py
  obtain ⟨u', du', su⟩ := H.s1 x dx
  obtain ⟨w, dw, aw⟩ := H.a1 u' y du' dy
  obtain ⟨w0, dw0, aw0⟩ := H.a1 x y dx dy
  obtain ⟨w1, dw1, sw⟩ := H.s1 w0 dw0
  exact ⟨w, w1, ⟨dw, u', y, ⟨du', x, px, su⟩, py, aw⟩, ⟨dw1, w0, ⟨dw0, x, y, px, py, aw0⟩, sw⟩,
    H3 x u' y w w0 w1 dx du' dy dw dw0 dw1 su aw aw0 sw⟩

theorem m_mulSucc (H : MTheta M)
    (H3 : ∀ u u' v w w0 w1 : M, mD u → mD u' → mD v → mD w → mD w0 → mD w1 →
      mS u u' → mMu u' v w → mMu u v w0 → mA v w0 w1 → mI w w1)
    {X Y : M → Prop} (hX : ∀ x, X x → mD x) (hY : ∀ x, Y x → mD x)
    (nX : ∃ v : M, X v) (nY : ∃ v : M, Y v) :
    mEqVal (mMulV (mSuccV X) Y) (mAddV Y (mMulV X Y)) := by
  obtain ⟨x, px⟩ := nX
  obtain ⟨y, py⟩ := nY
  have dx := hX x px
  have dy := hY y py
  obtain ⟨u', du', su⟩ := H.s1 x dx
  obtain ⟨w, dw, mw⟩ := H.m1 u' y du' dy
  obtain ⟨w0, dw0, mw0⟩ := H.m1 x y dx dy
  obtain ⟨w1, dw1, aw⟩ := H.a1 y w0 dy dw0
  exact ⟨w, w1, ⟨dw, u', y, ⟨du', x, px, su⟩, py, mw⟩,
    ⟨dw1, y, w0, py, ⟨dw0, x, y, px, py, mw0⟩, aw⟩,
    H3 x u' y w w0 w1 dx du' dy dw dw0 dw1 su mw mw0 aw⟩

theorem valid_cAdd (M : Type) [Nonempty M] [s : Structure NL M] : M↓[NL] ⊧ sWith fCAdd := by
  show ev (![] : Fin 0 → M) (sWith fCAdd)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fCAdd, ev_imp, ev_sEqVal, wOf_sAddV']
  exact m_cAdd H (wOf_sBox_dom 0) (wOf_sBox_dom 1) (wOf_sBox_dom 2) (wOf_sBox_dom 3)
theorem valid_cMul (M : Type) [Nonempty M] [s : Structure NL M] : M↓[NL] ⊧ sWith fCMul := by
  show ev (![] : Fin 0 → M) (sWith fCMul)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fCMul, ev_imp, ev_sEqVal, wOf_sMulV']
  exact m_cMul H (wOf_sBox_dom 0) (wOf_sBox_dom 1) (wOf_sBox_dom 2) (wOf_sBox_dom 3)
theorem valid_addSucc (M : Type) [Nonempty M] [s : Structure NL M] :
    M↓[NL] ⊧ sWith fAddSucc := by
  show ev (![] : Fin 0 → M) (sWith fAddSucc)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fAddSucc, ev_imp, ev_sEqVal, ev_sA3, ev_sNE, wOf_sAddV', wOf_sSuccV']
  exact fun H3 n0 n1 => m_addSucc H H3 (wOf_sBox_dom 0) (wOf_sBox_dom 1) n0 n1
theorem valid_mulSucc (M : Type) [Nonempty M] [s : Structure NL M] :
    M↓[NL] ⊧ sWith fMulSucc := by
  show ev (![] : Fin 0 → M) (sWith fMulSucc)
  refine (ev_sWith _).mpr fun H => ?_
  simp only [fMulSucc, ev_imp, ev_sEqVal, ev_sM3, ev_sNE, wOf_sAddV', wOf_sMulV', wOf_sSuccV']
  exact fun H3 n0 n1 => m_mulSucc H H3 (wOf_sBox_dom 1) (wOf_sBox_dom 0) n1 n0

end semantics

section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : Theory SourceL} [T.Δ₁]

theorem instS_sA3 (A : Fin 4 → Bootstrapping.Semiformula V SourceL 1) :
    instS (sig A) sA3 = tHyp sA3 := by simp [sA3, tHyp]
theorem instS_sM3 (A : Fin 4 → Bootstrapping.Semiformula V SourceL 1) :
    instS (sig A) sM3 = tHyp sM3 := by simp [sM3, tHyp]

/-- Under the domain guard of `&c`, the value formula of the variable `&c` has a member:
`&c` itself. -/
theorem ne_derivable (S : SourceFacts (V := V) T)
    (A : Fin 4 → Bootstrapping.Semiformula V SourceL 1) (i : Fin 4) (c : V)
    (hA : A i = tEq (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar c)) :
    GDerivable T (insert (instS (sig A) (sNE i)).val (∅ : V)) := by
  have ev : (instS (sig A) (sNE i)).val =
      ^∃ (domainCode (^#(0 : V)) ^⋏ equalityCode (^#(0 : V)) (^&c)) := by
    simp [sNE, hA]
  have hE : IsFormula SourceL (^∃ (domainCode (^#(0 : V)) ^⋏ equalityCode (^#(0 : V)) (^&c))) := by
    rw [← ev]
    simp
  have hp : IsSemiformula SourceL 1 (equalityCode (^#(0 : V)) (^&c)) :=
    equalityCode_valid (by simp) (by simp)
  have es : substs1 SourceL (^&c) (equalityCode (^#(0 : V)) (^&c)) =
      equalityCode (^&c) (^&c) := by
    have h := congrArg Bootstrapping.Semiformula.val
      (tEq_subst (Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V SourceL 1)
        (Bootstrapping.Semiterm.fvar c) ![(Bootstrapping.Semiterm.fvar c :
          Bootstrapping.Semiterm V SourceL 0)])
    rw [Bootstrapping.Semiformula.val_substs, tEq_val, tEq_val] at h
    simpa [substs1] using h
  have e1 : (tHyp sE1 : Bootstrapping.Semiformula V SourceL 0) =
      ∀⁰ (tEq (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 0)) := by
    simp [sE1, tHyp]
  have h0 := S.e1
  rw [e1] at h0
  have h1 := TProof.specialize! h0 (Bootstrapping.Semiterm.fvar c)
  rw [tEq_subst] at h1
  have g := gd0 h1
  have eg : (tEq ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V SourceL 1).subst
      ![(Bootstrapping.Semiterm.fvar c : Bootstrapping.Semiterm V SourceL 0)])
      ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V SourceL 1).subst
        ![(Bootstrapping.Semiterm.fvar c : Bootstrapping.Semiterm V SourceL 0)])).val =
      equalityCode (^&c) (^&c) := by simp
  rw [eg] at g
  have hEq : IsFormula SourceL (equalityCode (^&c : V) (^&c)) :=
    equalityCode_valid (by simp) (by simp)
  rw [ev]
  refine GDerivable.ex_rel hp (by simp) c ?_
  rw [es]
  exact GDerivable.wk (fs_cons hEq (fs_cons hE fs_nil)) (by set_tac) g

theorem two_cuts {N0 N1 X : V}
    (g : GDerivable T (insert (neg SourceL N0) (insert (neg SourceL N1) (insert X (∅ : V)))))
    (n0 : GDerivable T (insert N0 (∅ : V))) (n1 : GDerivable T (insert N1 (∅ : V))) :
    GDerivable T (insert X (∅ : V)) := by
  have hg := g.isFormulaSet
  have h1 := (IsFormulaSet.insert_iff.mp hg).2
  have fnN1 := (IsFormulaSet.insert_iff.mp h1).1
  have fX := (IsFormulaSet.insert_iff.mp (IsFormulaSet.insert_iff.mp h1).2).1
  have f0 := (IsFormulaSet.insert_iff.mp n0.isFormulaSet).1
  have f1 := (IsFormulaSet.insert_iff.mp n1.isFormulaSet).1
  have hΔ : IsFormulaSet SourceL (insert X (∅ : V)) := fs_cons fX fs_nil
  have inner : GDerivable T (insert (neg SourceL N1) (insert X (∅ : V))) :=
    GDerivable.cut_wk (fs_cons fnN1 hΔ) f0 n0 g (by set_tac) (by set_tac)
  exact GDerivable.cut_wk hΔ f1 n1 inner (by set_tac) (by set_tac)

section facts
variable (S : SourceFacts (V := V) T)
include S

theorem cong_add {s₁ s₁' s₂ s₂' : V} (h1 : IsSemiterm PA194PAeq.language 0 s₁)
    (h1' : IsSemiterm PA194PAeq.language 0 s₁') (h2 : IsSemiterm PA194PAeq.language 0 s₂)
    (h2' : IsSemiterm PA194PAeq.language 0 s₂') :
    GDerivable T (insert (neg SourceL (tr (peq s₁ s₁')))
      (insert (neg SourceL (tr (peq s₂ s₂')))
        (insert (tr (peq (addT s₁ s₂) (addT s₁' s₂'))) (∅ : V)))) := by
  obtain ⟨R1, e1⟩ := boxOf h1
  obtain ⟨R1', e1'⟩ := boxOf h1'
  obtain ⟨R2, e2⟩ := boxOf h2
  obtain ⟨R2', e2'⟩ := boxOf h2'
  obtain ⟨A, a0, a1, a2, a3⟩ := exA4 R1 R1' R2 R2'
  have h := with_facts A S fCAdd valid_cAdd
  simp only [fCAdd, instS_imp, instS_sEqVal, instS_sAddV, instS_sBox, a0, a1, a2, a3] at h
  have g := gd2 h
  rwa [tEqVal_tr h1 h1' e1 e1', tEqVal_tr h2 h2' e2 e2',
    tEqVal_tr (addT_valid h1 h2) (addT_valid h1' h2') (tAddV_val h1 h2 e1 e2)
      (tAddV_val h1' h2' e1' e2')] at g

theorem cong_mul {s₁ s₁' s₂ s₂' : V} (h1 : IsSemiterm PA194PAeq.language 0 s₁)
    (h1' : IsSemiterm PA194PAeq.language 0 s₁') (h2 : IsSemiterm PA194PAeq.language 0 s₂)
    (h2' : IsSemiterm PA194PAeq.language 0 s₂') :
    GDerivable T (insert (neg SourceL (tr (peq s₁ s₁')))
      (insert (neg SourceL (tr (peq s₂ s₂')))
        (insert (tr (peq (mulT s₁ s₂) (mulT s₁' s₂'))) (∅ : V)))) := by
  obtain ⟨R1, e1⟩ := boxOf h1
  obtain ⟨R1', e1'⟩ := boxOf h1'
  obtain ⟨R2, e2⟩ := boxOf h2
  obtain ⟨R2', e2'⟩ := boxOf h2'
  obtain ⟨A, a0, a1, a2, a3⟩ := exA4 R1 R1' R2 R2'
  have h := with_facts A S fCMul valid_cMul
  simp only [fCMul, instS_imp, instS_sEqVal, instS_sMulV, instS_sBox, a0, a1, a2, a3] at h
  have g := gd2 h
  rwa [tEqVal_tr h1 h1' e1 e1', tEqVal_tr h2 h2' e2 e2',
    tEqVal_tr (mulT_valid h1 h2) (mulT_valid h1' h2') (tMulV_val h1 h2 e1 e2)
      (tMulV_val h1' h2' e1' e2')] at g

theorem addSucc_open (hA3 : T.internalize V ⊢ (tHyp sA3 : Bootstrapping.Semiformula V SourceL 0))
    (a b : V) :
    GDerivable T (insert (tr (peq (addT (succT (^&a)) (^&b)) (succT (addT (^&a) (^&b)))))
      (∅ : V)) := by
  have ha : IsSemiterm PA194PAeq.language 0 (^&a : V) := by simp
  have hb : IsSemiterm PA194PAeq.language 0 (^&b : V) := by simp
  obtain ⟨A, a0, a1, -, -⟩ := exA4
    (tEq (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a) :
      Bootstrapping.Semiformula V SourceL 1)
    (tEq (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar b)) ⊤ ⊤
  have h := with_facts A S fAddSucc valid_addSucc
  simp only [fAddSucc, instS_imp] at h
  have g := gd2 (tmp h (by rw [instS_sA3]; exact hA3))
  have eX : (instS (sig A) (sEqVal (sAddV (sSuccV (sBox 0)) (sBox 1))
      (sSuccV (sAddV (sBox 0) (sBox 1))))).val =
      tr (peq (addT (succT (^&a)) (^&b)) (succT (addT (^&a) (^&b)))) := by
    simp only [instS_sEqVal, instS_sAddV, instS_sSuccV, instS_sBox, a0, a1]
    exact tEqVal_tr (addT_valid (succT_valid ha) hb) (succT_valid (addT_valid ha hb))
      (tAddV_val (succT_valid ha) hb (tSuccV_val ha (boxVar a)) (boxVar b))
      (tSuccV_val (addT_valid ha hb) (tAddV_val ha hb (boxVar a) (boxVar b)))
  rw [eX] at g
  exact two_cuts g (ne_derivable S A 0 a a0) (ne_derivable S A 1 b a1)

theorem mulSucc_open (hM3 : T.internalize V ⊢ (tHyp sM3 : Bootstrapping.Semiformula V SourceL 0))
    (a b : V) :
    GDerivable T (insert (tr (peq (mulT (succT (^&a)) (^&b)) (addT (^&b) (mulT (^&a) (^&b)))))
      (∅ : V)) := by
  have ha : IsSemiterm PA194PAeq.language 0 (^&a : V) := by simp
  have hb : IsSemiterm PA194PAeq.language 0 (^&b : V) := by simp
  obtain ⟨A, a0, a1, -, -⟩ := exA4
    (tEq (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar b) :
      Bootstrapping.Semiformula V SourceL 1)
    (tEq (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a)) ⊤ ⊤
  have h := with_facts A S fMulSucc valid_mulSucc
  simp only [fMulSucc, instS_imp] at h
  have g := gd2 (tmp h (by rw [instS_sM3]; exact hM3))
  have eX : (instS (sig A) (sEqVal (sMulV (sSuccV (sBox 1)) (sBox 0))
      (sAddV (sBox 0) (sMulV (sBox 1) (sBox 0))))).val =
      tr (peq (mulT (succT (^&a)) (^&b)) (addT (^&b) (mulT (^&a) (^&b)))) := by
    simp only [instS_sEqVal, instS_sAddV, instS_sMulV, instS_sSuccV, instS_sBox, a0, a1]
    exact tEqVal_tr (mulT_valid (succT_valid ha) hb) (addT_valid hb (mulT_valid ha hb))
      (tMulV_val (succT_valid ha) hb (tSuccV_val ha (boxVar a)) (boxVar b))
      (tAddV_val hb (mulT_valid ha hb) (boxVar b) (tMulV_val ha hb (boxVar a) (boxVar b)))
  rw [eX] at g
  exact two_cuts g (ne_derivable S A 0 b a0) (ne_derivable S A 1 a a1)

end facts

#print axioms ne_derivable
#print axioms cong_add
#print axioms cong_mul
#print axioms addSucc_open
#print axioms mulSucc_open
end generic

#print axioms valid_cAdd
#print axioms valid_cMul
#print axioms valid_addSucc
#print axioms valid_mulSucc
end PA194GuardedCompiler
