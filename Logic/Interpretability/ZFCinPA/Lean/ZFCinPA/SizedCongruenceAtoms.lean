import ZFCinPA.SizedCongruence

/-!
# The atom case of bounded equality replacement

`SizedCongruence.core` takes the atom case as the hypothesis `AtomOK A`. This
module proves it. Replacement in an atom `R(a₁, a₂) ⇒ R(b₁, b₂)` is an
instance of a fixed `𝗭𝗙` theorem

  `∀ x₁ y₁ x₂ y₂, x₁ = y₁ → x₂ = y₂ → R(x₁, x₂) → R(y₁, y₂)`,

whose meta-level proof has a *standard numeral* code (`proof_of_quote_proof`).
The instance is reached by four bounded specializations (`spec_step`), each
intermediate formula being a fixed formula under one substitution of closed
variable terms (`tsubst_le`), so its level is linear in the level `c` of the
terms. Identical coordinates use the reflexivity theorem `∀ x, x = x`.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedCongruenceAtoms

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.BoundedPAConsistency.SizedDerivation LeanProofs.BoundedPAConsistency.SubstBound
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation
open LeanProofs.ZFCinPA.SizedCongruence
open LeanProofs.ZFCinPA.SetCongruence (sEq sMem eqAtom memAtom quote_vec2_eta)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local prefix:max "#'" => Bootstrapping.Semiterm.bvar (V := V) (L := ℒₛₑₜ)
local infix:46 " ≐ₛ " => eqAtom

/-! ## Typed substitution bounds -/

theorem tvec_entries {k : ℕ} (v : Bootstrapping.SemitermVec V ℒₛₑₜ k 0) {c : V}
    (h : ∀ i, (v i).val ≤ lvB c) :
    (∀ i < (k : V), v.val.[i] ≤ lvB c) ∧ (∀ i < (k : V), IsVarTerm v.val.[i]) := by
  constructor
  · intro i hi
    obtain ⟨j, rfl⟩ := eq_fin_of_lt_nat hi
    rw [Bootstrapping.SemitermVec.val_nth_eq]
    exact h j
  · intro i hi
    obtain ⟨j, rfl⟩ := eq_fin_of_lt_nat hi
    rw [Bootstrapping.SemitermVec.val_nth_eq]
    exact closed_isVar (by simpa using (v j).isSemiterm)

theorem tsubst_le {k : ℕ} (ψ : Bootstrapping.Semiformula V ℒₛₑₜ k)
    (v : Bootstrapping.SemitermVec V ℒₛₑₜ k 0) {u c : V} (hψ : ψ.val ≤ lvB u) (hc : 1 ≤ c)
    (hv : ∀ i, (v i).val ≤ lvB c) : (ψ.subst v).val ≤ lvB (10 * (u + 1) + c) := by
  obtain ⟨hb, hvar⟩ := tvec_entries v hv
  rw [Bootstrapping.Semiformula.val_substs]
  exact subst_level u ψ.val hψ ψ.isSemiformula.isUFormula c k 0 v.val hc
    (by simpa using v.isSemitermVec) hb hvar

/-! ## Bounded specialization with level bookkeeping -/

theorem lt_of_level {x m w : V} (hx : x ≤ lvB m) (hw : m + 1 ≤ w) : x < lvB w :=
  lt_of_lt_of_le (lt_lvB_succ hx) (lvB_mono hw)

theorem le_ten {m : V} : m + 1 ≤ 10 * (m + 1) + 1 :=
  le_trans (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num)) le_self_add

theorem neg_lt_of_level {Z : Bootstrapping.Formula V ℒₛₑₜ} {m w : V} (hZ : Z.val ≤ lvB m)
    (hw : 10 * (m + 1) + 1 ≤ w) : (∼Z).val < lvB w := by
  rw [Bootstrapping.Semiformula.val_neg]
  exact lt_of_level (neg_level m _ hZ Z.isSemiformula.isUFormula) hw

/-- One bounded specialization, phrased through the closed forms `X` and `Y`
of the universal formula and its instance. -/
theorem spec_step {φ : Bootstrapping.Semiformula V ℒₛₑₜ 1} {t : Bootstrapping.Term V ℒₛₑₜ}
    {X Y : Bootstrapping.Formula V ℒₛₑₜ} {Γ w m : V}
    (hX : ∀⁰ φ = X) (hY : φ.subst ![t] = Y) (hXm : X.val ≤ lvB m) (hYm : Y.val ≤ lvB m)
    (htm : t.val ≤ lvB m) (hw : 10 * (m + 1) + 1 ≤ w) (hw4 : 4 ≤ w) (hΓ : SeqLt Γ w)
    (hfs : IsFormulaSet ℒₛₑₜ Γ) (h : DLv 𝗭𝗙 (insert X.val Γ) w) :
    DLv 𝗭𝗙 (insert Y.val Γ) (w + 3) := by
  subst hX hY
  have hw1 : m + 1 ≤ w := le_trans le_ten hw
  refine spec hw4 hΓ hfs (lt_of_level hXm hw1) (lt_of_level hYm hw1) ?_ (neg_lt_of_level hYm hw)
    (lt_of_level htm hw1) h
  rw [← Bootstrapping.Semiformula.neg_all]
  exact neg_lt_of_level hXm hw

/-! ## The fixed theorems and their numeral proofs -/

/-- `∀ x, x = x`. -/
def reflSent : SetTheorySentence := ∀⁰ sEq #0 #0

/-- `∀ x₁ y₁ x₂ y₂, x₁ = y₁ → x₂ = y₂ → r(x₁, x₂) → r(y₁, y₂)` (de Bruijn order). -/
def extSent (r : (ℒₛₑₜ).Rel 2) : SetTheorySentence :=
  ∀⁰ ∀⁰ ∀⁰ ∀⁰ (sEq #3 #2 🡒 sEq #1 #0 🡒 Semiformula.rel r ![#3, #1] 🡒 Semiformula.rel r ![#2, #0])

theorem zf_refl : 𝗭𝗙 ⊢ reflSent := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙 _ ?_
  intro M _ _ _
  simp [reflSent, models_iff, sEq]

theorem zf_ext (r : (ℒₛₑₜ).Rel 2) : 𝗭𝗙 ⊢ extSent r := by
  refine SetTheory.provable_of_models.{0} 𝗭𝗙 _ ?_
  intro M _ _ _
  cases r
  · simp [extSent, models_iff, sEq]
  · (simp [extSent, models_iff, sEq]; grind)

def reflProof : 𝗭𝗙 ⊢! reflSent := zf_refl.get
def extProof (r : (ℒₛₑₜ).Rel 2) : 𝗭𝗙 ⊢! extSent r := (zf_ext r).get

/-- The (standard) codes of the fixed proofs and sentences. -/
def reflD : ℕ := ⌜reflProof⌝
def reflN : ℕ := ⌜reflSent⌝
def extD (r : (ℒₛₑₜ).Rel 2) : ℕ := ⌜extProof r⌝
def extN (r : (ℒₛₑₜ).Rel 2) : ℕ := ⌜extSent r⌝

/-- The internal body of `reflSent`. -/
def reflBody : Bootstrapping.Semiformula V ℒₛₑₜ 1 := (#'0) ≐ₛ (#'0)

/-- The internal body of `extSent r`. -/
def extBody (r : (ℒₛₑₜ).Rel 2) : Bootstrapping.Semiformula V ℒₛₑₜ 4 :=
  ((#'3) ≐ₛ (#'2)) 🡒 ((#'1) ≐ₛ (#'0)) 🡒 Bootstrapping.Semiformula.rel r ![#'3, #'1] 🡒
    Bootstrapping.Semiformula.rel r ![#'2, #'0]

theorem refl_quote : (⌜reflSent⌝ : Bootstrapping.Formula V ℒₛₑₜ) = ∀⁰ reflBody := by
  rw [Sentence.typed_quote_def]
  simp [reflSent, reflBody, sEq, eqAtom, Rew.q_emb, Rew.emb_bvar, quote_vec2_eta]

theorem ext_quote (r : (ℒₛₑₜ).Rel 2) :
    (⌜extSent r⌝ : Bootstrapping.Formula V ℒₛₑₜ) = ∀⁰ ∀⁰ ∀⁰ ∀⁰ extBody r := by
  rw [Sentence.typed_quote_def]
  simp [extSent, extBody, sEq, eqAtom, Rew.q_emb, Rew.emb_bvar, quote_vec2_eta]

theorem refl_dlv : DLv 𝗭𝗙 (insert (∀⁰ reflBody : Bootstrapping.Formula V ℒₛₑₜ).val ∅)
    (reflD : V) := by
  have hp : Proof 𝗭𝗙 (⌜reflProof⌝ : V) ⌜reflSent⌝ := proof_of_quote_proof reflProof
  rw [Sentence.quote_eq, refl_quote] at hp
  rw [← singleton_eq_insert]
  unfold reflD
  rw [coe_quote_proof_eq]
  exact DLv.of_derivationOf hp

theorem ext_dlv (r : (ℒₛₑₜ).Rel 2) :
    DLv 𝗭𝗙 (insert (∀⁰ ∀⁰ ∀⁰ ∀⁰ extBody r : Bootstrapping.Formula V ℒₛₑₜ).val ∅) (extD r : V) := by
  have hp : Proof 𝗭𝗙 (⌜extProof r⌝ : V) ⌜extSent r⌝ := proof_of_quote_proof (extProof r)
  rw [Sentence.quote_eq, ext_quote] at hp
  rw [← singleton_eq_insert]
  unfold extD
  rw [coe_quote_proof_eq]
  exact DLv.of_derivationOf hp

theorem refl_le : (∀⁰ reflBody : Bootstrapping.Formula V ℒₛₑₜ).val ≤ lvB (reflN : V) := by
  rw [← refl_quote, ← Sentence.quote_eq, reflN, Sentence.coe_quote_eq_quote]
  exact le_lvB_self _

theorem ext_le (r : (ℒₛₑₜ).Rel 2) :
    (∀⁰ ∀⁰ ∀⁰ ∀⁰ extBody r : Bootstrapping.Formula V ℒₛₑₜ).val ≤ lvB (extN r : V) := by
  rw [← ext_quote, ← Sentence.quote_eq, extN, Sentence.coe_quote_eq_quote]
  exact le_lvB_self _

theorem body_le {k : ℕ} {φ : Bootstrapping.Semiformula V ℒₛₑₜ (k + 1)} {u : V}
    (h : (∀⁰ φ).val ≤ lvB u) : φ.val ≤ lvB u :=
  le_trans (le_of_lt (by simpa using lt_forall φ.val)) h

/-! ## The bounded instances -/

/-- A closed raw term as a typed term. -/
def mkT (a : V) (ha : IsSemiterm ℒₛₑₜ 0 a) : Bootstrapping.Term V ℒₛₑₜ := ⟨a, by simpa using ha⟩

@[simp] theorem mkT_val (a : V) (ha : IsSemiterm ℒₛₑₜ 0 a) : (mkT a ha).val = a := rfl

theorem eqAtom_val (t u : Bootstrapping.Term V ℒₛₑₜ) :
    (t ≐ₛ u).val = ^rel 2 (0 : V) (t.val ∷ u.val ∷ 0) := by
  rw [SetCongruence.val_eqAtom, SetCongruence.coe_setEqIndex_eq]

theorem one_le_of_le {x y : V} (h : 1 ≤ x) (hxy : x ≤ y) : 1 ≤ y := le_trans h hxy

/-- **Reflexivity, bounded**: `a = a` joins any sequent at four levels above
the working level `w`. -/
theorem refl_leaf {a Γ c w : V} (ha : IsSemiterm ℒₛₑₜ 0 a) (hac : a ≤ lvB c) (hc : 1 ≤ c)
    (hw : 10 * (10 * ((reflN : V) + 1) + c + 1) + 1 ≤ w) (hwD : (reflD : V) ≤ w) (hw4 : 4 ≤ w)
    (hΓ : SeqLt Γ w) (hfs : IsFormulaSet ℒₛₑₜ Γ) :
    DLv 𝗭𝗙 (insert (^rel 2 (0 : V) (a ∷ a ∷ 0)) Γ) (w + 1 + 3) := by
  set t := mkT a ha
  set m := 10 * ((reflN : V) + 1) + c with hm
  have hNm : (reflN : V) ≤ m := le_trans (le_trans le_self_add
    (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))) le_self_add
  have hX : (∀⁰ reflBody : Bootstrapping.Formula V ℒₛₑₜ).val ≤ lvB m := lift_lvB refl_le hNm
  have hY : (reflBody.subst ![t]).val ≤ lvB m :=
    tsubst_le reflBody ![t] (body_le refl_le) hc (fun i => by rcases Fin.eq_zero i with rfl; simpa [t] using hac)
  have htm : t.val ≤ lvB m := lift_lvB hac le_add_self
  have hw1 : m + 1 ≤ w := le_trans le_ten hw
  have d0 : DLv 𝗭𝗙 (insert (∀⁰ reflBody : Bootstrapping.Formula V ℒₛₑₜ).val Γ) (w + 1) :=
    DLv.wk hw4 (hΓ.insert (lt_of_level hX hw1)) (formulaSet_insert hfs)
      (insert_subset_insert_of_subset _ (by intro z hz; simp at hz)) (refl_dlv.mono hwD)
  have d1 := spec_step (X := (∀⁰ reflBody : Bootstrapping.Formula V ℒₛₑₜ)) rfl rfl hX hY htm
    (le_trans hw le_self_add) (le_trans hw4 le_self_add) (hΓ.mono le_self_add) hfs d0
  have hval : (reflBody.subst ![t]).val = ^rel 2 (0 : V) (a ∷ a ∷ 0) := by
    simp [reflBody, t, SetCongruence.setEqIndex_eq_zero]
  rwa [hval] at d1

theorem vec1_le {t₁ : Bootstrapping.Term V ℒₛₑₜ} {c : V} (h₁ : t₁.val ≤ lvB c) :
    ∀ i, (![t₁] i).val ≤ lvB c := fun i => by rcases Fin.eq_zero i with rfl; exact h₁

theorem vec2_le {t₁ t₂ : Bootstrapping.Term V ℒₛₑₜ} {c : V} (h₁ : t₁.val ≤ lvB c)
    (h₂ : t₂.val ≤ lvB c) : ∀ i, (![t₁, t₂] i).val ≤ lvB c := fun i => by
  match i with
  | 0 => exact h₁
  | 1 => exact h₂

theorem vec3_le {t₁ t₂ t₃ : Bootstrapping.Term V ℒₛₑₜ} {c : V} (h₁ : t₁.val ≤ lvB c)
    (h₂ : t₂.val ≤ lvB c) (h₃ : t₃.val ≤ lvB c) : ∀ i, (![t₁, t₂, t₃] i).val ≤ lvB c := fun i => by
  match i with
  | 0 => exact h₁
  | 1 => exact h₂
  | 2 => exact h₃

theorem vec4_le {t₁ t₂ t₃ t₄ : Bootstrapping.Term V ℒₛₑₜ} {c : V} (h₁ : t₁.val ≤ lvB c)
    (h₂ : t₂.val ≤ lvB c) (h₃ : t₃.val ≤ lvB c) (h₄ : t₄.val ≤ lvB c) :
    ∀ i, (![t₁, t₂, t₃, t₄] i).val ≤ lvB c := fun i => by
  match i with
  | 0 => exact h₁
  | 1 => exact h₂
  | 2 => exact h₃
  | 3 => exact h₄

theorem le_ext_m (r : (ℒₛₑₜ).Rel 2) (c : V) : (extN r : V) ≤ 10 * ((extN r : V) + 1) + c :=
  le_trans (le_trans le_self_add (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num)))
    le_self_add

theorem subst_q_sing {k : ℕ} (ψ : Bootstrapping.Semiformula V ℒₛₑₜ (k + 1))
    (v : Bootstrapping.SemitermVec V ℒₛₑₜ k 0) (t : Bootstrapping.Term V ℒₛₑₜ) :
    (ψ.subst v.q).subst ![t] = ψ.subst (t :> v) := by
  rw [Bootstrapping.Semiformula.substs_substs]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ j => simp

/-- **The extensionality instance, bounded**: four specializations. -/
theorem ext_chain (r : (ℒₛₑₜ).Rel 2) {Γ c w : V} (ta₁ ta₂ tb₁ tb₂ : Bootstrapping.Term V ℒₛₑₜ)
    (h₁ : ta₁.val ≤ lvB c) (h₂ : ta₂.val ≤ lvB c) (h₃ : tb₁.val ≤ lvB c) (h₄ : tb₂.val ≤ lvB c)
    (hc : 1 ≤ c) (hw : 10 * (10 * ((extN r : V) + 1) + c + 1) + 1 ≤ w) (hwD : (extD r : V) ≤ w)
    (hw4 : 4 ≤ w) (hΓ : SeqLt Γ w) (hfs : IsFormulaSet ℒₛₑₜ Γ) :
    DLv 𝗭𝗙 (insert ((extBody r).subst ![tb₂, ta₂, tb₁, ta₁]).val Γ) (w + 1 + 3 + 3 + 3 + 3) := by
  set θ := extBody (V := V) r
  set m := 10 * ((extN r : V) + 1) + c with hm
  have hN := ext_le (V := V) r
  have hN3 := body_le hN
  have hN2 := body_le hN3
  have hN1 := body_le hN2
  have hNm := le_ext_m r c
  have hX₀ : (∀⁰ ∀⁰ ∀⁰ ∀⁰ θ : Bootstrapping.Formula V ℒₛₑₜ).val ≤ lvB m := lift_lvB hN hNm
  have hY₁ : ((∀⁰ ∀⁰ ∀⁰ θ).subst ![ta₁]).val ≤ lvB m := tsubst_le _ _ hN3 hc (vec1_le h₁)
  have hY₂ : ((∀⁰ ∀⁰ θ).subst ![tb₁, ta₁]).val ≤ lvB m := tsubst_le _ _ hN2 hc (vec2_le h₃ h₁)
  have hY₃ : ((∀⁰ θ).subst ![ta₂, tb₁, ta₁]).val ≤ lvB m :=
    tsubst_le _ _ hN1 hc (vec3_le h₂ h₃ h₁)
  have hY₄ : (θ.subst ![tb₂, ta₂, tb₁, ta₁]).val ≤ lvB m :=
    tsubst_le _ _ (body_le hN1) hc (vec4_le h₄ h₂ h₃ h₁)
  have hcm : c ≤ m := le_add_self
  have hw1 : m + 1 ≤ w := le_trans le_ten hw
  have d0 : DLv 𝗭𝗙 (insert (∀⁰ ∀⁰ ∀⁰ ∀⁰ θ : Bootstrapping.Formula V ℒₛₑₜ).val Γ) (w + 1) :=
    DLv.wk hw4 (hΓ.insert (lt_of_level hX₀ hw1)) (formulaSet_insert hfs)
      (insert_subset_insert_of_subset _ (by intro z hz; simp at hz)) ((ext_dlv r).mono hwD)
  have up : ∀ k : V, 10 * (m + 1) + 1 ≤ w + k := fun k => le_trans hw le_self_add
  have up4 : ∀ k : V, 4 ≤ w + k := fun k => le_trans hw4 le_self_add
  have d1 := spec_step (φ := ∀⁰ ∀⁰ ∀⁰ θ) (t := ta₁) rfl rfl hX₀ hY₁ (lift_lvB h₁ hcm) (up 1) (up4 1)
    (hΓ.mono le_self_add) hfs d0
  have d2 := spec_step (φ := (∀⁰ ∀⁰ θ).subst (Bootstrapping.SemitermVec.q ![ta₁])) (t := tb₁)
    (Bootstrapping.Semiformula.substs_all _ _).symm
    (subst_q_sing _ _ _) hY₁ hY₂ (lift_lvB h₃ hcm)
    (by simpa [add_assoc] using up (1 + 3)) (by simpa [add_assoc] using up4 (1 + 3))
    (hΓ.mono (by simpa [add_assoc] using (le_self_add : w ≤ w + (1 + 3)))) hfs d1
  have d3 := spec_step (φ := (∀⁰ θ).subst (Bootstrapping.SemitermVec.q ![tb₁, ta₁])) (t := ta₂)
    (Bootstrapping.Semiformula.substs_all _ _).symm
    (subst_q_sing _ _ _) hY₂ hY₃ (lift_lvB h₂ hcm)
    (by simpa [add_assoc] using up (1 + 3 + 3)) (by simpa [add_assoc] using up4 (1 + 3 + 3))
    (hΓ.mono (by simpa [add_assoc] using (le_self_add : w ≤ w + (1 + 3 + 3)))) hfs d2
  exact spec_step (φ := θ.subst (Bootstrapping.SemitermVec.q ![ta₂, tb₁, ta₁])) (t := tb₂)
    (Bootstrapping.Semiformula.substs_all _ _).symm
    (subst_q_sing _ _ _) hY₃ hY₄ (lift_lvB h₄ hcm)
    (by simpa [add_assoc] using up (1 + 3 + 3 + 3)) (by simpa [add_assoc] using up4 (1 + 3 + 3 + 3))
    (hΓ.mono (by simpa [add_assoc] using (le_self_add : w ≤ w + (1 + 3 + 3 + 3)))) hfs d3

theorem ext_inst (r : (ℒₛₑₜ).Rel 2) (ta₁ ta₂ tb₁ tb₂ : Bootstrapping.Term V ℒₛₑₜ) :
    (extBody r).subst ![tb₂, ta₂, tb₁, ta₁] =
      ((ta₁ ≐ₛ tb₁) 🡒 (ta₂ ≐ₛ tb₂) 🡒 Bootstrapping.Semiformula.rel r ![ta₁, ta₂] 🡒
        Bootstrapping.Semiformula.rel r ![tb₁, tb₂]) := by
  simp [extBody, eqAtom]

/-! ## The atom case -/

/-- The working level of the atom derivation. -/
def aW (r : (ℒₛₑₜ).Rel 2) (c : V) : V :=
  (extD r : V) + reflD + 10 * (10 * ((extN r : V) + reflN + 1) + c + 12) + 1

/-- The constant of the atom case. -/
def atomA (r : (ℒₛₑₜ).Rel 2) : V := (extD r : V) + reflD + 100 * ((extN r : V) + reflN) + 235

/-- The member level of the atom derivation. -/
def aM (r : (ℒₛₑₜ).Rel 2) (c : V) : V := 10 * (10 * ((extN r : V) + 1) + c + 1)

section levels

variable (r : (ℒₛₑₜ).Rel 2) (c : V)

theorem aM_aW : aM r c + 1 ≤ aW r c :=
  le_of_add_eq (y := (extD r : V) + reflD + 100 * reflN + 110) (by unfold aM aW; ring)

theorem aW_refl : 10 * (10 * ((reflN : V) + 1) + c + 1) + 1 ≤ aW r c :=
  le_of_add_eq (y := (extD r : V) + reflD + 100 * extN r + 110) (by unfold aW; ring)

theorem aW_extD : (extD r : V) ≤ aW r c :=
  le_of_add_eq (y := (reflD : V) + 10 * (10 * ((extN r : V) + reflN + 1) + c + 12) + 1)
    (by unfold aW; ring)

theorem aW_reflD : (reflD : V) ≤ aW r c :=
  le_of_add_eq (y := (extD r : V) + 10 * (10 * ((extN r : V) + reflN + 1) + c + 12) + 1)
    (by unfold aW; ring)

theorem aW_four : 4 ≤ aW r c :=
  le_of_add_eq (y := (extD r : V) + reflD + 100 * ((extN r : V) + reflN) + 10 * c + 217)
    (by unfold aW; ring)

theorem aW_atomA : aW r c + 1 + 13 = atomA r + 10 * c := by unfold aW atomA; ring

theorem atom_aM : c + 1 + 10 ≤ aM r c :=
  le_of_add_eq (y := 100 * (extN r : V) + 9 * c + 99) (by unfold aM; ring)

theorem ext_m_aM : 10 * (10 * ((extN r : V) + 1) + c + 1) ≤ aM r c := le_rfl

end levels

theorem atom_le {tag R a b c : V} (hc : 1 ≤ c) (ht : tag ≤ 1) (hR : R = 0 ∨ R = 1)
    (ha : a ≤ lvB c) (hb : b ≤ lvB c) : ⟪tag, 2, R, a ∷ b ∷ 0⟫ + 1 ≤ lvB (c + 1 + 10) :=
  atom_rebuild (show (2 : V) ≤ c + 1 from le_trans (by norm_num : (2 : V) ≤ 1 + 1)
    (_root_.add_le_add hc le_rfl)) ht
    (by rcases hR with rfl | rfl <;> simp) (lift_lvB ha le_self_add) (lift_lvB hb le_self_add)

theorem neg_eq_atom {a b : V} (ha : IsSemiterm ℒₛₑₜ 0 a) (hb : IsSemiterm ℒₛₑₜ 0 b) :
    neg ℒₛₑₜ (^rel 2 (0 : V) (a ∷ b ∷ 0)) = neR a b := by
  unfold neR
  exact neg_rel (isRel_R (Or.inl rfl)) (by simp [ha.isUTerm, hb.isUTerm])

set_option maxHeartbeats 1000000 in
/-- **The atom case for one relation symbol.** -/
theorem atom_for (r : (ℒₛₑₜ).Rel 2) (R : V) (hR : R = 0 ∨ R = 1)
    (hr : ∀ t u : Bootstrapping.Term V ℒₛₑₜ,
      (Bootstrapping.Semiformula.rel r ![t, u]).val = ^rel 2 R (t.val ∷ u.val ∷ 0))
    (hrn : ∀ t u : Bootstrapping.Term V ℒₛₑₜ,
      (Bootstrapping.Semiformula.nrel r ![t, u]).val = ^nrel 2 R (t.val ∷ u.val ∷ 0))
    {a₁ a₂ b₁ b₂ E c : V} (hc : 1 ≤ c)
    (ha₁ : IsSemiterm ℒₛₑₜ 0 a₁) (ha₂ : IsSemiterm ℒₛₑₜ 0 a₂)
    (hb₁ : IsSemiterm ℒₛₑₜ 0 b₁) (hb₂ : IsSemiterm ℒₛₑₜ 0 b₂)
    (la₁ : a₁ ≤ lvB c) (la₂ : a₂ ≤ lvB c) (lb₁ : b₁ ≤ lvB c) (lb₂ : b₂ ≤ lvB c)
    (hE : IsFormulaSet ℒₛₑₜ E) (hEb : SeqLe E c) (hP₁ : Pair1 E a₁ b₁) (hP₂ : Pair1 E a₂ b₂) :
    DLv 𝗭𝗙 (insert (^nrel 2 R (a₁ ∷ a₂ ∷ 0)) (insert (^rel 2 R (b₁ ∷ b₂ ∷ 0)) E))
      (atomA r + 10 * c) := by
  set ta₁ := mkT a₁ ha₁
  set ta₂ := mkT a₂ ha₂
  set tb₁ := mkT b₁ hb₁
  set tb₂ := mkT b₂ hb₂
  set w := aW r c with hwdef
  set MM := aM r c
  have hMw : MM + 1 ≤ w := aM_aW r c
  have hw4 : 4 ≤ w := aW_four r c
  -- the sequent `Γ`
  set Γ := insert (^nrel 2 R (a₁ ∷ a₂ ∷ 0)) (insert (^rel 2 R (b₁ ∷ b₂ ∷ 0)) E) with hΓdef
  have nA : ^nrel 2 R (a₁ ∷ a₂ ∷ 0) = (Bootstrapping.Semiformula.nrel r ![ta₁, ta₂]).val :=
    (hrn ta₁ ta₂).symm
  have rB : ^rel 2 R (b₁ ∷ b₂ ∷ 0) = (Bootstrapping.Semiformula.rel r ![tb₁, tb₂]).val :=
    (hr tb₁ tb₂).symm
  have hcM : c ≤ MM := le_trans (le_trans le_self_add le_self_add) (atom_aM r c)
  have hΓl : SeqLe Γ MM :=
    SeqLe.insert (lift_lvB (atom_le hc le_rfl hR la₁ la₂) (atom_aM r c))
      (SeqLe.insert (lift_lvB (atom_le hc (by simp) hR lb₁ lb₂) (atom_aM r c))
        (hEb.mono hcM))
  have hΓf : IsFormulaSet ℒₛₑₜ Γ := by
    rw [hΓdef, nA, rB]
    exact formulaSet_insert (formulaSet_insert hE)
  -- the instance `I` and its negation
  set I : Bootstrapping.Formula V ℒₛₑₜ := (ta₁ ≐ₛ tb₁) 🡒 (ta₂ ≐ₛ tb₂) 🡒
    Bootstrapping.Semiformula.rel r ![ta₁, ta₂] 🡒 Bootstrapping.Semiformula.rel r ![tb₁, tb₂]
    with hIdef
  have dI : DLv 𝗭𝗙 (insert I.val Γ) (w + 1 + 3 + 3 + 3 + 3) := by
    rw [hIdef, ← ext_inst]
    exact ext_chain r ta₁ ta₂ tb₁ tb₂ la₁ la₂ lb₁ lb₂ hc hMw
      (aW_extD r c) hw4 (hΓl.toLt hMw) hΓf
  have hIm : I.val ≤ lvB (10 * ((extN r : V) + 1) + c) := by
    rw [hIdef, ← ext_inst]
    exact tsubst_le _ _ (body_le (body_le (body_le (body_le (ext_le r))))) hc
      (vec4_le lb₂ la₂ lb₁ la₁)
  have hNm : (∼I).val ≤ lvB MM := by
    rw [Bootstrapping.Semiformula.val_neg]
    exact neg_level _ _ hIm I.isSemiformula.isUFormula
  set P₁ := ^rel 2 (0 : V) (a₁ ∷ b₁ ∷ 0)
  set P₂ := ^rel 2 (0 : V) (a₂ ∷ b₂ ∷ 0)
  set Ra := ^rel 2 R (a₁ ∷ a₂ ∷ 0)
  set nRb := ^nrel 2 R (b₁ ∷ b₂ ∷ 0)
  have hshape : (∼I).val = P₁ ^⋏ (P₂ ^⋏ (Ra ^⋏ nRb)) := by
    have e1 : ∼I = (ta₁ ≐ₛ tb₁) ⋏ ((ta₂ ≐ₛ tb₂) ⋏ (Bootstrapping.Semiformula.rel r ![ta₁, ta₂] ⋏
        Bootstrapping.Semiformula.nrel r ![tb₁, tb₂])) := by
      simp [hIdef, Bootstrapping.Semiformula.imp_def]
    rw [e1]
    simp only [Bootstrapping.Semiformula.val_and]
    rw [eqAtom_val, eqAtom_val, hr, hrn]
    rfl
  have hNf : IsFormula ℒₛₑₜ (P₁ ^⋏ (P₂ ^⋏ (Ra ^⋏ nRb))) := by
    rw [← hshape]; exact (∼I).isSemiformula
  have fP₁ : IsFormula ℒₛₑₜ P₁ := (IsSemiformula.and.mp hNf).1
  have fQ₁ : IsFormula ℒₛₑₜ (P₂ ^⋏ (Ra ^⋏ nRb)) := (IsSemiformula.and.mp hNf).2
  have fP₂ : IsFormula ℒₛₑₜ P₂ := (IsSemiformula.and.mp fQ₁).1
  have fQ₂ : IsFormula ℒₛₑₜ (Ra ^⋏ nRb) := (IsSemiformula.and.mp fQ₁).2
  have fRa : IsFormula ℒₛₑₜ Ra := (IsSemiformula.and.mp fQ₂).1
  have fnRb : IsFormula ℒₛₑₜ nRb := (IsSemiformula.and.mp fQ₂).2
  have lN : P₁ ^⋏ (P₂ ^⋏ (Ra ^⋏ nRb)) ≤ lvB MM := hshape ▸ hNm
  have lQ₁ : P₂ ^⋏ (Ra ^⋏ nRb) ≤ lvB MM := le_trans (le_of_lt (lt_K!_right _ _)) lN
  have lQ₂ : Ra ^⋏ nRb ≤ lvB MM := le_trans (le_of_lt (lt_K!_right _ _)) lQ₁
  have lP₁ : P₁ ≤ lvB MM := le_trans (le_of_lt (lt_K!_left _ _)) lN
  have lP₂ : P₂ ≤ lvB MM := le_trans (le_of_lt (lt_K!_left _ _)) lQ₁
  have lRa : Ra ≤ lvB MM := le_trans (le_of_lt (lt_K!_left _ _)) lQ₂
  have lnRb : nRb ≤ lvB MM := le_trans (le_of_lt (lt_K!_right _ _)) lQ₂
  -- the sequents of the negative side
  set S₀ := insert (P₁ ^⋏ (P₂ ^⋏ (Ra ^⋏ nRb))) Γ with hS₀
  set S₁ := insert (P₂ ^⋏ (Ra ^⋏ nRb)) S₀ with hS₁
  set S₂ := insert (Ra ^⋏ nRb) S₁ with hS₂
  have lS₀ : SeqLe S₀ MM := hΓl.insert lN
  have lS₁ : SeqLe S₁ MM := lS₀.insert lQ₁
  have lS₂ : SeqLe S₂ MM := lS₁.insert lQ₂
  have fS₀ : IsFormulaSet ℒₛₑₜ S₀ := by simp [hS₀, hNf, hΓf]
  have fS₁ : IsFormulaSet ℒₛₑₜ S₁ := by simp [hS₁, fQ₁, fS₀]
  have fS₂ : IsFormulaSet ℒₛₑₜ S₂ := by simp [hS₂, fQ₂, fS₁]
  have sΓ₂ : Γ ⊆ S₂ := fun z hz => by simp [hS₂, hS₁, hS₀, hz]
  have sE : ∀ {S : V}, Γ ⊆ S → E ⊆ S := fun hS z hz => hS (by simp [hΓdef, hz])
  -- equality leaves
  have eq_leaf : ∀ {a b S : V}, IsSemiterm ℒₛₑₜ 0 a → IsSemiterm ℒₛₑₜ 0 b → a ≤ lvB c →
      Pair1 E a b → Γ ⊆ S → SeqLe S MM → IsFormulaSet ℒₛₑₜ S →
      ^rel 2 (0 : V) (a ∷ b ∷ 0) ≤ lvB MM → IsFormula ℒₛₑₜ (^rel 2 (0 : V) (a ∷ b ∷ 0)) →
      DLv 𝗭𝗙 (insert (^rel 2 (0 : V) (a ∷ b ∷ 0)) S) (w + 1 + 3) := by
    intro a b S ha hb hac hP hΓS hSl hSf hl hf
    rcases hP with rfl | ⟨h₁, -⟩
    · exact refl_leaf ha hac hc (aW_refl r c) (aW_reflD r c) hw4 (hSl.toLt hMw) hSf
    · refine (DLv.em hw4 ((hSl.insert hl).toLt hMw) (by simp [hf, hSf]) (^rel 2 (0 : V) (a ∷ b ∷ 0))
        (mem_bitInsert_iff.mpr (Or.inl rfl)) ?_).mono (by simpa [add_assoc] using (le_self_add : w + 1 ≤ w + 1 + 3))
      rw [neg_eq_atom ha hb]
      exact mem_bitInsert_iff.mpr (Or.inr (sE hΓS h₁))
  have dP₁ := eq_leaf ha₁ hb₁ la₁ hP₁ (fun z hz => by simp [hS₀, hz]) lS₀ fS₀ lP₁ fP₁
  have dP₂ := eq_leaf ha₂ hb₂ la₂ hP₂ (fun z hz => by simp [hS₁, hS₀, hz]) lS₁ fS₁ lP₂ fP₂
  -- the two atom leaves
  have dRa : DLv 𝗭𝗙 (insert Ra S₂) (w + 1) := by
    refine DLv.em hw4 ((lS₂.insert lRa).toLt hMw) (by simp [fRa, fS₂]) Ra (by simp) ?_
    have : neg ℒₛₑₜ Ra = ^nrel 2 R (a₁ ∷ a₂ ∷ 0) :=
      neg_rel (isRel_R hR) (by simp [ha₁.isUTerm, ha₂.isUTerm])
    rw [this]
    exact mem_bitInsert_iff.mpr (Or.inr (sΓ₂ (by simp [hΓdef])))
  have dnRb : DLv 𝗭𝗙 (insert nRb S₂) (w + 1) := by
    refine DLv.em hw4 ((lS₂.insert lnRb).toLt hMw) (by simp [fnRb, fS₂]) nRb (by simp) ?_
    have : neg ℒₛₑₜ nRb = ^rel 2 R (b₁ ∷ b₂ ∷ 0) :=
      neg_nrel (isRel_R hR) (by simp [hb₁.isUTerm, hb₂.isUTerm])
    rw [this]
    exact mem_bitInsert_iff.mpr (Or.inr (sΓ₂ (by simp [hΓdef])))
  have hw4' : ∀ k : V, 4 ≤ w + k := fun k => le_trans hw4 le_self_add
  have hMk : ∀ k : V, MM + 1 ≤ w + k := fun k => le_trans hMw le_self_add
  have m13 : w + 1 ≤ w + 1 + 3 := le_self_add
  have dQ₂ : DLv 𝗭𝗙 S₂ (w + 1 + 3 + 1) :=
    DLv.and_m (by simpa [add_assoc] using hw4' (1 + 3)) (lS₂.toLt (by simpa [add_assoc] using hMk (1 + 3)))
      (p := Ra) (q := nRb) (by simp [hS₂]) (dRa.mono m13) (dnRb.mono m13)
  have dQ₁ : DLv 𝗭𝗙 S₁ (w + 1 + 3 + 1 + 1) :=
    DLv.and_m (by simpa [add_assoc] using hw4' (1 + 3 + 1))
      (lS₁.toLt (by simpa [add_assoc] using hMk (1 + 3 + 1)))
      (p := P₂) (q := Ra ^⋏ nRb) (by simp [hS₁]) (dP₂.mono le_self_add) dQ₂
  have dS₀ : DLv 𝗭𝗙 S₀ (w + 1 + 3 + 1 + 1 + 1) :=
    DLv.and_m (by simpa [add_assoc] using hw4' (1 + 3 + 1 + 1))
      (lS₀.toLt (by simpa [add_assoc] using hMk (1 + 3 + 1 + 1)))
      (p := P₁) (q := P₂ ^⋏ (Ra ^⋏ nRb)) (by simp [hS₀])
      (dP₁.mono (le_trans le_self_add le_self_add)) dQ₁
  -- the cut on `I`
  have hm₀ : 10 * ((extN r : V) + 1) + c ≤ MM :=
    le_trans le_self_add (le_mul_of_one_le_left (Arithmetic.zero_le _) (by norm_num))
  have hcut := DLv.cut (T := 𝗭𝗙) (by simpa [add_assoc] using hw4' (1 + 3 + 3 + 3 + 3))
    (hΓl.toLt (by simpa [add_assoc] using hMk (1 + 3 + 3 + 3 + 3))) I.val
    (lt_of_level (lift_lvB hIm hm₀) (by simpa [add_assoc] using hMk (1 + 3 + 3 + 3 + 3)))
    dI (by
      rw [← Bootstrapping.Semiformula.val_neg, hshape]
      exact dS₀.mono (le_of_add_eq (y := 6) (by ring)))
  exact hcut.mono (le_of_eq (by rw [← aW_atomA r c]; ring))

/-! ## The oracle, and unconditional replacement -/

theorem rel_eq_val (t u : Bootstrapping.Term V ℒₛₑₜ) :
    (Bootstrapping.Semiformula.rel Language.Set.Rel.eq ![t, u]).val = ^rel 2 (0 : V) (t.val ∷ u.val ∷ 0) :=
  eqAtom_val t u

theorem nrel_eq_val (t u : Bootstrapping.Term V ℒₛₑₜ) :
    (Bootstrapping.Semiformula.nrel Language.Set.Rel.eq ![t, u]).val =
      ^nrel 2 (0 : V) (t.val ∷ u.val ∷ 0) := by
  rw [show Bootstrapping.Semiformula.nrel Language.Set.Rel.eq ![t, u] = SetCongruence.neAtom t u from rfl,
    SetCongruence.val_neAtom, SetCongruence.coe_setEqIndex_eq]

theorem rel_mem_val (t u : Bootstrapping.Term V ℒₛₑₜ) :
    (Bootstrapping.Semiformula.rel Language.Set.Rel.mem ![t, u]).val =
      ^rel 2 (1 : V) (t.val ∷ u.val ∷ 0) := by
  rw [show Bootstrapping.Semiformula.rel Language.Set.Rel.mem ![t, u] = SetCongruence.memAtom t u from rfl,
    SetCongruence.val_memAtom, SetCongruence.coe_setMemIndex_eq]

theorem nrel_mem_val (t u : Bootstrapping.Term V ℒₛₑₜ) :
    (Bootstrapping.Semiformula.nrel Language.Set.Rel.mem ![t, u]).val =
      ^nrel 2 (1 : V) (t.val ∷ u.val ∷ 0) := by
  rw [show Bootstrapping.Semiformula.nrel Language.Set.Rel.mem ![t, u] = SetCongruence.nmemAtom t u from rfl,
    SetCongruence.val_nmemAtom, SetCongruence.coe_setMemIndex_eq]

/-- The atom constant for `ℒₛₑₜ`: a standard number. -/
def congA : V := atomA Language.Set.Rel.eq + atomA Language.Set.Rel.mem

/-- **The atom oracle holds.** -/
theorem atomOK : AtomOK (congA : V) := by
  intro R a₁ a₂ b₁ b₂ E c hR hc ha₁ ha₂ hb₁ hb₂ la₁ la₂ lb₁ lb₂ hE hEb hP₁ hP₂
  rcases hR with rfl | rfl
  · exact (atom_for Language.Set.Rel.eq 0 (Or.inl rfl) rel_eq_val nrel_eq_val hc ha₁ ha₂ hb₁ hb₂
      la₁ la₂ lb₁ lb₂ hE hEb hP₁ hP₂).mono (_root_.add_le_add le_self_add le_rfl)
  · exact (atom_for Language.Set.Rel.mem 1 (Or.inr rfl) rel_mem_val nrel_mem_val hc ha₁ ha₂ hb₁ hb₂
      la₁ la₂ lb₁ lb₂ hE hEb hP₁ hP₂).mono (_root_.add_le_add le_add_self le_rfl)

/-- **Bounded equality replacement, unconditional.** For every internal
semiformula `χ` of complexity at most `h` and code level `v`, and closed
vectors `w₁`, `w₂` paired through `E` at level `c`, the sequent
`¬χ[w₁], χ[w₂], E` has a `𝗭𝗙`-derivation with code at most
`2^(lvB (30h + 10c + 100v + congA + 200))`. -/
theorem replace_le (v : V) : ∀ h χ n w₁ w₂ E c : V,
    formulaComplexity ℒₛₑₜ χ ≤ h → IsSemiformula ℒₛₑₜ n χ → χ ≤ lvB v → Inp n w₁ w₂ E c →
    DLv 𝗭𝗙 (Cseq w₁ w₂ χ E) (cW congA v h c) :=
  core atomOK v

end LeanProofs.ZFCinPA.SizedCongruenceAtoms
