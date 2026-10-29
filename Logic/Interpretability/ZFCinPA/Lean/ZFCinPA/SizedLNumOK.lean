import ZFCinPA.SizedLGlue1
import ZFCinPA.LNumOK

/-!
# Bounded numeral chains: `numOK` on the level scale

`LNumOK.numOK` proves `𝗭𝗙 ⊢ NumOKT (numChainQ x)` (the `x`-th von Neumann
numeral chain defines exactly one natural number) by a `Σ₁` induction on `x`:
the base compiles `numBaseTemplate`, each step compiles `numStepTemplate` and
applies it to the previous proof and the definitional premise, a tautology
`∀(N ↔ N)` at the chain's own codes. This module proves the bounded twin
`numOK_le` on the level scale `DLv`.

* `numChain_le`: `numChainCode x ≤ lvB (Cn + 6x)`. One chain step is an
  existential over a conjunction, three pairings, six levels.
* `imp_ante_le`, `dmdpL`, `dk_introL`, `K6_le`, `top_le`: the combinators of
  `SizedLGlue1` driven by level bounds instead of strict code bounds, and the
  placeholder-tuple bound for the six-placeholder step language.
* `numOK_le`: for a target `J`, every placeholder up to `J` is at level
  `uN J = Cn + 6J`, so the induction runs at one fixed compile level and each
  step adds `10` levels.
-/
set_option autoImplicit false
noncomputable section

namespace LeanProofs.ZFCinPA.SizedLNumOK

open LO LO.FirstOrder LO.FirstOrder.SetTheory LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA
open LeanProofs.BoundedPAConsistency.SizedDerivation
open LeanProofs.ZFCinPA.SetCodeLevels LeanProofs.ZFCinPA.LevelDerivation
open LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.TemplateTranslateLevel
open LeanProofs.ZFCinPA.SizedCongruence (lt_lvB_succ le_of_add_eq)
open LeanProofs.ZFCinPA.SizedLPlumbing LeanProofs.ZFCinPA.SizedLGlue1
open LeanProofs.ZFCinPA.LTemplate LeanProofs.ZFCinPA.LInvariant LeanProofs.ZFCinPA.LStepAnd
open LeanProofs.ZFCinPA.LStepAtom LeanProofs.ZFCinPA.LDriverBase LeanProofs.ZFCinPA.LNumOK
open LeanProofs.ZFCinPA.NumeralOmega (numZeroS succRelS numChainQ numChainQ_zero numChainQ_succ
  numChainQ_val)
open LeanProofs.ZFCinPA.SizedOpenTemplateLeaves (cExpG)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local notation "Fm" => Bootstrapping.Formula V ℒₛₑₜ

/-! ## Level-driven combinators -/

/-- The antecedent of an implication of level `m` has level `10(m+1)`. -/
theorem imp_ante_le {φ ψ : Fm} {m : V} (h : (φ 🡒 ψ).val ≤ lvB m) :
    φ.val ≤ lvB (10 * (m + 1)) := by
  have himp : (φ 🡒 ψ).val = (∼φ).val ^⋎ ψ.val := by
    rw [Bootstrapping.Semiformula.imp_def, Bootstrapping.Semiformula.val_or]
  have hlt : (∼φ).val < (φ 🡒 ψ).val := by rw [himp]; exact lt_or_left _ _
  have := neg_level _ _ (le_trans hlt.le h) (∼φ).isSemiformula.isUFormula
  rw [← Bootstrapping.Semiformula.val_neg] at this
  simpa using this

/-- Modus ponens at an implication of level `m`. -/
theorem dmdpL {φ ψ : Fm} {w m : V} (hw : 4 ≤ w) (hm : (φ 🡒 ψ).val ≤ lvB m)
    (hmw : 10 * (m + 1) + 1 ≤ w) (d1 : DLv 𝗭𝗙 (insert (φ 🡒 ψ).val ∅) w)
    (d2 : DLv 𝗭𝗙 (insert φ.val ∅) w) : DLv 𝗭𝗙 (insert ψ.val ∅) (w + 1 + 1 + 1) := by
  have hneg : (∼(φ 🡒 ψ)) = φ ⋏ ∼ψ := by simp [Bootstrapping.Semiformula.imp_def]
  have hn : (φ ⋏ ∼ψ).val < lvB w := by
    rw [← hneg, Bootstrapping.Semiformula.val_neg]
    exact lt_of_lt_of_le (lt_lvB_succ (neg_level _ _ hm (φ 🡒 ψ).isSemiformula.isUFormula))
      (lvB_mono hmw)
  have hi : (φ 🡒 ψ).val < lvB w :=
    lt_of_lt_of_le (lt_lvB_succ hm)
      (lvB_mono (le_trans (le_of_add_eq (y := 9 * m + 10) (by ring)) hmw))
  exact dmdp hw hn hi d1 d2

/-- `∧`-introduction at a conjunction of level `m`. -/
theorem dk_introL {φ ψ : Fm} {w m : V} (hw : 4 ≤ w) (hm : (φ ⋏ ψ).val ≤ lvB m) (hmw : m + 1 ≤ w)
    (d1 : DLv 𝗭𝗙 (insert φ.val ∅) w) (d2 : DLv 𝗭𝗙 (insert ψ.val ∅) w) :
    DLv 𝗭𝗙 (insert (φ ⋏ ψ).val ∅) (w + 1 + 1) :=
  dk_intro hw (lt_of_lt_of_le (lt_lvB_succ hm) (lvB_mono hmw)) d1 d2

theorem and_left_le {φ ψ : Fm} {m : V} (h : (φ ⋏ ψ).val ≤ lvB m) : φ.val ≤ lvB m :=
  le_trans (lt_K!_left _ _).le h

theorem and_right_le {φ ψ : Fm} {m : V} (h : (φ ⋏ ψ).val ≤ lvB m) : ψ.val ≤ lvB m :=
  le_trans (lt_K!_right _ _).le h

/-- `∧`-elimination (right) at a conjunction of level `m`, by a cut on it. -/
theorem dk_rightL {φ ψ : Fm} {w m : V} (hw : 4 ≤ w) (hm : (φ ⋏ ψ).val ≤ lvB m)
    (hmw : 10 * (m + 1) + 1 ≤ w) (d : DLv 𝗭𝗙 (insert (φ ⋏ ψ).val ∅) w) :
    DLv 𝗭𝗙 (insert ψ.val ∅) (w + 1 + 1 + 1) := by
  have hmw' : m + 1 ≤ w := le_trans (le_of_add_eq (y := 9 * m + 10) (by ring)) hmw
  have hp : (φ ⋏ ψ).val < lvB w := lt_of_lt_of_le (lt_lvB_succ hm) (lvB_mono hmw')
  have hψ : ψ.val < lvB w := lt_trans (lt_K!_right _ _) hp
  have hneg : (∼(φ ⋏ ψ)).val < lvB w := by
    rw [Bootstrapping.Semiformula.val_neg]
    exact lt_of_lt_of_le (lt_lvB_succ (neg_level _ _ hm (φ ⋏ ψ).isSemiformula.isUFormula))
      (lvB_mono hmw)
  have hnn : (∼(φ ⋏ ψ)) = ∼φ ⋎ ∼ψ := by simp
  have e1 : (∼φ).val < (∼(φ ⋏ ψ)).val := by
    rw [hnn, Bootstrapping.Semiformula.val_or]; exact lt_or_left _ _
  have e2 : (∼ψ).val < (∼(φ ⋏ ψ)).val := by
    rw [hnn, Bootstrapping.Semiformula.val_or]; exact lt_or_right _ _
  set S := insert ψ.val (∅ : V) with hSd
  have lS : SeqLt S w := (SeqLt.empty w).insert hψ
  have fS : IsFormulaSet ℒₛₑₜ S := fset1 ψ
  set B := insert (∼(φ ⋏ ψ)).val S with hBd
  have lB : SeqLt B w := lS.insert hneg
  have fB : IsFormulaSet ℒₛₑₜ B := fins _ fS
  have dE : DLv 𝗭𝗙 (insert (∼φ).val (insert (∼ψ).val B)) (w + 1) := by
    refine DLv.em hw ((lB.insert (lt_trans e2 hneg)).insert (lt_trans e1 hneg))
      (fins _ (fins _ fB)) ψ.val (by simp [hBd, hSd]) ?_
    rw [← Bootstrapping.Semiformula.val_neg]; simp
  have dO : DLv 𝗭𝗙 B (w + 1 + 1) := by
    refine DLv.or_m (le_trans hw le_self_add) (lB.mono le_self_add) (p := (∼φ).val)
      (q := (∼ψ).val) ?_ dE
    rw [hBd, hnn, Bootstrapping.Semiformula.val_or]; simp
  have dA : DLv 𝗭𝗙 (insert (φ ⋏ ψ).val S) (w + 1) :=
    DLv.wk hw (lS.insert hp) (fins _ fS)
      (insert_subset_insert_of_subset _ (by intro z hz; simp at hz)) d
  have hneg' : neg ℒₛₑₜ (φ ⋏ ψ).val = (∼(φ ⋏ ψ)).val := (Bootstrapping.Semiformula.val_neg _).symm
  exact DLv.cut (le_trans hw (le_trans le_self_add le_self_add))
    (lS.mono (le_trans le_self_add le_self_add)) (φ ⋏ ψ).val
    (lt_of_lt_of_le hp (lvB_mono (le_trans le_self_add le_self_add))) (dA.mono le_self_add)
    (by rw [hneg']; exact dO)

theorem top_le {n : ℕ} {u : V} (hu : 2 ≤ u) : (⊤ : SF V n).val ≤ lvB u := by
  simpa using SizedPlaceholderCongruence.verum_le hu

/-- A six-placeholder tuple at level `u`. -/
theorem K6_le {u : V} {p₀ p₂ p₄ : SF V 1} {f₁ f₃ f₅ : SF V 2}
    (h0 : p₀.val ≤ lvB u) (h1 : f₁.val ≤ lvB u) (h2 : p₂.val ≤ lvB u) (h3 : f₃.val ≤ lvB u)
    (h4 : p₄.val ≤ lvB u) (h5 : f₅.val ≤ lvB u) : ∀ i, (K6 p₀ f₁ p₂ f₃ p₄ f₅ i).val ≤ lvB u
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3
  | ⟨4, _⟩ => h4
  | ⟨5, _⟩ => h5

/-! ## The level of a numeral chain -/

/-- The constant of the numeral-chain bound. -/
def Cn : V := (numChainZeroCode : V) + (numChainStepCode : V) + 2

/-- **Numeral chains grow by six levels per step.** -/
theorem numChain_le (x : V) : numChainCode x ≤ lvB (Cn + 6 * x) := by
  induction x using ISigma1.sigma1_succ_induction
  · simp only [lvB]
    definability
  · simp only [numChainCode_zero, mul_zero, add_zero]
    exact lift_lvB (le_lvB_self _) (le_trans le_self_add le_self_add)
  · case succ x ih =>
    rw [numChainCode_succ]
    have hu : (2 : V) ≤ Cn + 6 * x := le_trans le_add_self le_self_add
    have hc : ((numChainStepCode : ℕ) : V) ≤ lvB (Cn + 6 * x) :=
      lift_lvB (le_lvB_self _) (le_trans (le_trans le_add_self le_self_add) le_self_add)
    have a1 := pair_lvB' hu ih hc
    have a2 := pair_lvB (le_trans hu le_self_add)
      (tag_le_lvB (k := 4) (by norm_num) (le_trans hu le_self_add)) a1
    have a3 := pair_lvB (le_trans hu (le_trans le_self_add le_self_add))
      (tag_le_lvB (k := 7) (by norm_num) (le_trans hu (le_trans le_self_add le_self_add))) a2
    exact le_trans a3 (lvB_mono (le_of_eq (by ring)))

/-- The placeholder level of the numeral induction up to `J`. -/
def uN (J : V) : V := Cn + 6 * J

theorem two_le_uN (J : V) : (2 : V) ≤ uN J := le_trans le_add_self le_self_add

theorem numQ_le {x J : V} (h : x ≤ J) : (numChainQ x).val ≤ lvB (uN J) := by
  rw [numChainQ_val]
  exact lift_lvB (numChain_le x)
    (_root_.add_le_add le_rfl (mul_le_mul_of_nonneg_left h (by norm_num)))

theorem zeroQ_le (J : V) : (⌜numZeroS⌝ : SF V 1).val ≤ lvB (uN J) := by
  rw [← numChainQ_zero]; exact numQ_le (Arithmetic.zero_le J)

/-! ## The bounded induction -/

/-- The translation constant of the two numeral templates. -/
def tN : ℕ := tA (Rewriting.emb numBaseTemplate : Proposition L6) +
  tA (Rewriting.emb numStepTemplate : Proposition L6) + tA (Rewriting.emb numOK₀ : Proposition L6)

/-- The member level of the numeral induction. -/
def mN (J : V) : V := (tN : V) * (uN J + 1)

/-- The compile levels of the two numeral templates at `uN J`. -/
def cB (J : V) : V := cExpG (tmA numBaseTemplate_provable) (tmB numBaseTemplate_provable) (uN J) +
  (tmK numBaseTemplate_provable : ℕ) + 1

def cS (J : V) : V := cExpG (tmA numStepTemplate_provable) (tmB numStepTemplate_provable) (uN J) +
  (tmK numStepTemplate_provable : ℕ) + 1

/-- The base level of the bounded numeral induction. -/
def wN (J : V) : V := cB J + cS J + 100 * (mN J + 1) + 100 * uN J + 300

/-- **The level of `numOK`.** -/
def numW (j : V) : V := wN j + 10 * j

theorem trN_le {J : V} (σ : Sentence L6) (hσ : tA (Rewriting.emb σ : Proposition L6) ≤ tN)
    (Ks : (i : Fin 6) → SF V (ar6 i)) (hK : ∀ i, (Ks i).val ≤ lvB (uN J)) :
    (translateFormula Ks (Rewriting.emb σ)).val ≤ lvB (mN J) :=
  lift_lvB (translate_level _ (uN J) Ks hK)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hσ) (Arithmetic.zero_le _))

/-- `NumOKT (numChainQ x)`, on codes. -/
def numOKVal (x : V) : V := (NumOKT (numChainQ x)).val

instance numOKVal_definable : 𝚺₁-Function₁ (numOKVal : V → V) :=
  HierarchySymbol.DefinableFunction.of_eq _ (fun _ ↦ rfl) numOK_definable

set_option maxHeartbeats 4000000 in
/-- **Every numeral chain defines one natural number, bounded**, at every index
up to a target `J`, at the compile level of `J`. -/
theorem numOK_leJ {i₀ J : V} (h₀ : i₀ ≤ J) :
    DLv 𝗭𝗙 (insert (NumOKT (numChainQ i₀)).val ∅) (wN J + 10 * i₀) := by
  obtain ⟨W0, hW0⟩ : ∃ W0 : V, W0 = wN J := ⟨_, rfl⟩
  have hu2 := two_le_uN J
  have key : ∀ i : V, i ≤ J → DLv 𝗭𝗙 (insert (numOKVal i) ∅) (W0 + 10 * i) := by
    intro i
    induction i using ISigma1.sigma1_succ_induction
    · simp only [DLv, DerivableLe, lvB]
      definability
    · intro _
      have hK := K6_le (zeroQ_le J) (top_le hu2) (top_le hu2) (top_le hu2) (top_le hu2) (top_le hu2)
      have lt := trN_le numBaseTemplate (by unfold tN; omega) _ hK
      have hc := compiledLe (by decide) numBaseTemplate_provable _ hu2 hK
      rw [tr_numBase] at lt hc
      have d2 := dall_iff (⌜numZeroS⌝ : SF V 1) (zeroQ_le J) hu2
      set w := cB J + cS J + 100 * (mN J + 1) + 100 * uN J + 290 with hw
      have hw4 : (4 : V) ≤ w :=
        le_of_add_eq (y := cB J + cS J + 100 * (mN J + 1) + 100 * uN J + 286) (by rw [hw]; ring)
      have d := dmdpL hw4 lt
        (le_of_add_eq (y := cB J + cS J + 90 * mN J + 100 * uN J + 379) (by rw [hw]; ring))
        (hc.mono (show cB J ≤ w from
          le_of_add_eq (y := cS J + 100 * (mN J + 1) + 100 * uN J + 290) (by rw [hw]; ring)))
        (d2.mono (le_of_add_eq (y := cB J + cS J + 100 * (mN J + 1) + 52) (by rw [hw]; ring)))
      show DLv 𝗭𝗙 (insert (NumOKT (numChainQ 0)).val ∅) _
      rw [numChainQ_zero]
      refine d.mono ?_
      rw [hW0, hw]; unfold wN
      exact le_of_add_eq (y := 7) (by ring)
    · case succ i ih =>
      intro hiJ
      have hi : i ≤ J := le_trans le_self_add hiJ
      have d0 : DLv 𝗭𝗙 (insert (NumOKT (numChainQ i)).val ∅) (W0 + 10 * i) := ih hi
      set w := W0 + 10 * i with hw
      have hW : wN J ≤ w := by rw [hw, hW0]; exact le_self_add
      have hw4 : (4 : V) ≤ w := le_trans (le_of_add_eq
        (y := cB J + cS J + 100 * (mN J + 1) + 100 * uN J + 296) (by unfold wN; ring)) hW
      have hmw : 10 * (mN J + 1) + 1 ≤ w := le_trans (le_of_add_eq
        (y := cB J + cS J + 90 * mN J + 100 * uN J + 389) (by unfold wN; ring)) hW
      have hK := K6_le (numQ_le hi) (top_le hu2) (numQ_le hiJ) (top_le hu2) (top_le hu2) (top_le hu2)
      have lt := trN_le numStepTemplate (by unfold tN; omega) _ hK
      have hc := compiledLe (by decide) numStepTemplate_provable _ hu2 hK
      rw [tr_numStep] at lt hc
      -- the definitional premise
      have d2 := (dall_iff (numChainQ (i + 1)) (numQ_le hiJ) hu2).mono (le_trans (le_of_add_eq
        (y := cB J + cS J + 100 * (mN J + 1) + 62) (by unfold wN; ring)) hW)
      rw [show (∀⁰ (numChainQ (i + 1) 🡘 numChainQ (i + 1)) : Fm) =
          ∀⁰ (numChainQ (i + 1) 🡘 (∃⁰ ((numChainQ i).subst
            (![Bootstrapping.Semiterm.bvar 0] : Bootstrapping.SemitermVec V ℒₛₑₜ 1 2) ⋏
              ⌜succRelS⌝))) by rw [← numChainQ_succ]] at d2
      -- the conjunction and modus ponens
      have d3 := dk_introL hw4 (imp_ante_le lt) hmw d0 d2
      have up2 : w ≤ w + 1 + 1 := le_trans le_self_add le_self_add
      have d4 := dmdpL (le_trans hw4 up2) lt (le_trans hmw up2)
        (hc.mono (show cS J ≤ w + 1 + 1 from le_trans (le_trans (le_of_add_eq
          (y := cB J + 100 * (mN J + 1) + 100 * uN J + 300) (by unfold wN; ring)) hW) up2)) d3
      show DLv 𝗭𝗙 (insert (NumOKT (numChainQ (i + 1))).val ∅) _
      refine d4.mono ?_
      rw [hw]
      exact le_of_add_eq (y := 5) (by ring)
  have := key i₀ h₀
  rw [hW0] at this
  exact this

/-- **Every numeral chain defines one natural number, bounded.** -/
theorem numOK_le (J : V) : DLv 𝗭𝗙 (insert (NumOKT (numChainQ J)).val ∅) (numW J) :=
  numOK_leJ le_rfl

/-! ## The right half: the numeral's members are natural numbers -/

theorem numOKT_le {a J : V} (h : a ≤ J) : (NumOKT (numChainQ a)).val ≤ lvB (mN J) :=
  trN_le numOK₀ (by unfold tN; omega) _
    (K6_le (numQ_le h) (top_le (two_le_uN J)) (top_le (two_le_uN J)) (top_le (two_le_uN J))
      (top_le (two_le_uN J)) (top_le (two_le_uN J)))

theorem numOKT_split (N : SF V 1) : ∃ A : Fm, NumOKT N = A ⋏ (∀⁰ (∼N ⋎ ⌜LStepAtom.natP⌝)) := by
  have h : NumOKT N = NumOKT N := rfl
  conv at h => rhs; simp [NumOKT, LStepAtom.numOK₀, LStepAnd.P₀, translateFormula]
  exact ⟨_, h⟩

/-- The bounded twin of `LGlue1.numOK_right`. -/
theorem numOK_right_leJ {a J : V} (h : a ≤ J) :
    DLv 𝗭𝗙 (insert (∀⁰ (∼(numChainQ a) ⋎ ⌜LStepAtom.natP⌝) : Fm).val ∅)
      (wN J + 10 * a + 1 + 1 + 1) := by
  obtain ⟨A, hA⟩ := numOKT_split (numChainQ a)
  have d := numOK_leJ h
  have hm := numOKT_le h
  rw [hA] at d hm
  have hw : wN J ≤ wN J + 10 * a := le_self_add
  exact dk_rightL (le_trans (le_of_add_eq
      (y := cB J + cS J + 100 * (mN J + 1) + 100 * uN J + 296) (by unfold wN; ring)) hw) hm
    (le_trans (le_of_add_eq (y := cB J + cS J + 90 * mN J + 100 * uN J + 389)
      (by unfold wN; ring)) hw) d

end LeanProofs.ZFCinPA.SizedLNumOK
