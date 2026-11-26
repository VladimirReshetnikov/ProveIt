import IPRADerivations.Analysis.Names.LogisticName
import IPRADerivations.Analysis.RationalArithmetic.RationalSupMetric
import IPRADerivations.AnalyticNumberTheory.Order
import IPRADerivations.Core.CommonLemmas

/-!
# Gcd reduction and literal integer outputs of rational normalization

The actual normalizer divides the two canonical signed numerator parts and
the positive denominator by their computed gcd. Its rational value is
preserved. If the input value is an integer, the output is literally the
canonical integer code, not merely an equal rational value. This is the
code-equality dependency needed for arbitrary-formula midpoint replacement
in Minkowski's proof. General uniqueness of reduced rational codes is not
assumed or asserted here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalIntegerNormalization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Foundations.GapDecision (zabs)
open LeanProofs.IPRA.DiophantineNumberTheory
open LeanProofs.IPRA.AnalyticNumberTheory.Order (gcd_pos_right)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def positivePart (a : ZT n) : PTm n := monus a.pos a.neg
def negativePart (a : ZT n) : PTm n := monus a.neg a.pos

@[simp] theorem subst_positivePart {k : ℕ} (σ : Fin n → PTm k) (a : ZT n) :
    Syn.subst σ (positivePart a) = positivePart (a.subst σ) := by simp [positivePart, ZT.subst]
@[simp] theorem subst_negativePart {k : ℕ} (σ : Fin n → PTm k) (a : ZT n) :
    Syn.subst σ (negativePart a) = negativePart (a.subst σ) := by simp [negativePart, ZT.subst]

theorem parts_value (a : ZT n) : Γ ⊢[PRAAx] ZT.eq (⟨positivePart a,negativePart a⟩ : ZT n) a :=
  (monus_max a.pos a.neg).eqTrans (add_comm _ _)

theorem positivePart_congr {a b : ZT n} (h : Γ ⊢[PRAAx] ZT.eq a b) :
    Γ ⊢[PRAAx] positivePart a ≐ positivePart b :=
  (monus_add_add a.pos a.neg b.neg).eqSymm.eqTrans
    ((congrMonus h (add_comm _ _)).eqTrans (monus_add_add b.pos b.neg a.neg))

theorem negativePart_congr {a b : ZT n} (h : Γ ⊢[PRAAx] ZT.eq a b) :
    Γ ⊢[PRAAx] negativePart a ≐ negativePart b :=
  positivePart_congr (a := -a) (b := -b) (by
    apply ZT.derive
    simpa only [ZT.toZ_neg] using congrArg Neg.neg (ZT.toZ_eq h))

alias positive_form := Common.pos_of_one_le

def divisor (a : ZT n) (D : PTm n) : PTm n := gcd (zabs a) D
def reducedNumerator (a : ZT n) (D : PTm n) : ZT n :=
  ⟨quo (positivePart a) (divisor a D),quo (negativePart a) (divisor a D)⟩
def reducedDenominator (a : ZT n) (D : PTm n) : PTm n := quo D (divisor a D)
def normalize (a : ZT n) (D : PTm n) : PTm n :=
  pairT (pairT (reducedNumerator a D).pos (reducedNumerator a D).neg) (pred (reducedDenominator a D))
def integerCode (a : ZT n) : PTm n := pairT (pairT (positivePart a) (negativePart a)) zero

@[simp] theorem subst_divisor {k : ℕ} (σ : Fin n → PTm k) (a : ZT n) (D : PTm n) :
    Syn.subst σ (divisor a D) = divisor (a.subst σ) (Syn.subst σ D)  := by
  simp only [divisor, subst_ex2, Foundations.GapDecision.subst_zabs, ConciseIPRA.PTm.subst_succ]
@[simp] theorem subst_reducedNumerator {k : ℕ} (σ : Fin n → PTm k) (a : ZT n) (D : PTm n) :
    (reducedNumerator a D).subst σ = reducedNumerator (a.subst σ) (Syn.subst σ D) := by
  simp [reducedNumerator, ZT.subst]
@[simp] theorem subst_reducedDenominator {k : ℕ} (σ : Fin n → PTm k) (a : ZT n) (D : PTm n) :
    Syn.subst σ (reducedDenominator a D) = reducedDenominator (a.subst σ) (Syn.subst σ D) := by
  simp [reducedDenominator]
@[simp] theorem subst_normalize {k : ℕ} (σ : Fin n → PTm k) (a : ZT n) (D : PTm n) :
    Syn.subst σ (normalize a D) = normalize (a.subst σ) (Syn.subst σ D) := by
  simp [normalize, reducedNumerator]
@[simp] theorem subst_integerCode {k : ℕ} (σ : Fin n → PTm k) (a : ZT n) :
    Syn.subst σ (integerCode a) = integerCode (a.subst σ) := by simp [integerCode]

theorem divisor_positive (a : ZT n) (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] divisor a D ≐ succ (pred (divisor a D)) := gcd_pos_right (positive_form hD)

theorem divides_parts (a : ZT n) (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] dvd (divisor a D) (positivePart a) ⋏ dvd (divisor a D) (negativePart a) := by
  have g := divisor_positive a D hD
  have abs := Prf.andE₁ (gcd_dvd_at g)
  have dz : Γ ⊢[PRAAx] dvd (divisor a D) zero :=
    Coprime.dvd_of_eq' g (w := zero) (mul_zero _).eqSymm
  refine .orE (le_total a.pos a.neg) ?_ ?_
  · have e : (le a.pos a.neg :: Γ) ⊢[PRAAx] positivePart a ≐ zero := Prf.hyp0
    have value : (le a.pos a.neg :: Γ) ⊢[PRAAx] zabs a ≐ negativePart a :=
      (congrAdd e (.eqRefl _)).eqTrans (zero_add _)
    exact .andI (dvd_congr e.eqSymm dz.wk) (dvd_congr value abs.wk)
  · have e : (le a.neg a.pos :: Γ) ⊢[PRAAx] negativePart a ≐ zero := Prf.hyp0
    have value : (le a.neg a.pos :: Γ) ⊢[PRAAx] zabs a ≐ positivePart a :=
      (congrAdd (.eqRefl _) e).eqTrans (add_zero _)
    exact .andI (dvd_congr value abs.wk) (dvd_congr e.eqSymm dz.wk)

theorem reduced_denominator_identity (a : ZT n) (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] D ≐ divisor a D*reducedDenominator a D :=
  Coprime.eq_of_dvd' (divisor_positive a D hD) (Prf.andE₂ (gcd_dvd_at (divisor_positive a D hD)))

theorem reduced_numerator_identity (a : ZT n) (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] ZT.eq a (ZT.ofNat (divisor a D)*reducedNumerator a D) := by
  have parts := divides_parts a D hD
  have p := natEq (Coprime.eq_of_dvd' (divisor_positive a D hD) (Prf.andE₁ parts))
  have q := natEq (Coprime.eq_of_dvd' (divisor_positive a D hD) (Prf.andE₂ parts))
  have value := ZT.toZ_eq (parts_value (Γ := Γ) a)
  apply ZT.derive
  simp only [ZT.toZ_mul, ZT.toZ_ofNat]
  simp only [reducedNumerator, ZT.toZ] at value ⊢
  ipra_simps
  linear_combination -value+p-q

theorem reduced_denominator_positive (a : ZT n) (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] le one (reducedDenominator a D) := by
  refine .orE (zero_or_succ (reducedDenominator a D)) ?_ ?_
  · have hzero := (reduced_denominator_identity a D hD.wk).eqTrans
      ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))
    exact lt_zero_absurd _ (lt_congr (.eqRefl zero) hzero hD.wk)
  · exact le_of_eq_add (d := pred (reducedDenominator a D)) (Prf.hyp0.eqTrans (by ipra_ring))

theorem normalize_numerator (a : ZT n) (D : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (numeratorOf (normalize a D)) (reducedNumerator a D) :=
  RationalSupMetric.rationalCode_numerator _ _

theorem normalize_denominator (a : ZT n) (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] denominatorOf (normalize a D) ≐ reducedDenominator a D :=
  RationalSupMetric.rationalCode_denominator _ _ (reduced_denominator_positive a D hD)

theorem normalize_preserves_value (a : ZT n) (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] ZT.eq (a*ZT.ofNat (denominatorOf (normalize a D)))
      (numeratorOf (normalize a D)*ZT.ofNat D) := by
  have num := ZT.toZ_eq (normalize_numerator (Γ := Γ) a D)
  have den := natEq (normalize_denominator a D hD)
  have aeq := ZT.toZ_eq (reduced_numerator_identity a D hD)
  have deq := natEq (reduced_denominator_identity a D hD)
  apply ZT.derive
  simp only [ZT.toZ_mul, ZT.toZ_ofNat] at aeq ⊢
  rw [num, den, aeq, deq]
  simp only [Q.mk_mul, map_mul]
  ring

theorem gcd_multiple (a D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] gcd (D*a) D ≐ D := by
  have hd := positive_form hD
  have hg := gcd_pos_right (a := D*a) hd
  have parts := gcd_dvd_at hg
  have self := Coprime.dvd_self' hd
  have multiple := Coprime.dvd_of_eq' hd (w := a) (.eqRefl _)
  exact le_antisymm (Coprime.dvd_le' hg (Prf.andE₂ parts) hd)
    (Coprime.dvd_le' hd (Coprime.gcd_greatest' hd multiple self) hg)

theorem quotient_multiple (a D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] quo (D*a) D ≐ a := by
  have hd := positive_form hD
  have found := Prf.andE₁ (div_mod_unique
    (q := a) (r := zero) (K' := pred D)
    ((add_zero _).eqSymm.eqTrans (congrAdd (congrMul hd (.eqRefl _)) (.eqRefl _)))
    (lt_congr (.eqRefl zero) hd (show Γ ⊢[PRAAx] lt zero D from hD)))
  exact (congrAp2 quoF (.eqRefl _) hd).eqTrans found

theorem scaled_parts (a z : ZT n) (D : PTm n) (h : Γ ⊢[PRAAx] ZT.eq a (ZT.ofNat D*z)) :
    Γ ⊢[PRAAx] (positivePart a ≐ D*positivePart z) ⋏ (negativePart a ≐ D*negativePart z) := by
  have pos : Γ ⊢[PRAAx] (ZT.ofNat D*z).pos ≐ D*z.pos := by
    change Γ ⊢[PRAAx] D*z.pos+zero*z.neg ≐ D*z.pos
    ipra_ring
  have neg : Γ ⊢[PRAAx] (ZT.ofNat D*z).neg ≐ D*z.neg := by
    change Γ ⊢[PRAAx] D*z.neg+zero*z.pos ≐ D*z.neg
    ipra_ring
  have p : Γ ⊢[PRAAx] positivePart (ZT.ofNat D*z) ≐ monus (D*z.pos) (D*z.neg) := congrMonus pos neg
  have q : Γ ⊢[PRAAx] negativePart (ZT.ofNat D*z) ≐ monus (D*z.neg) (D*z.pos) := congrMonus neg pos
  exact .andI ((positivePart_congr h).eqTrans (p.eqTrans (LogisticName.monus_scale _ _ _)))
    ((negativePart_congr h).eqTrans (q.eqTrans (LogisticName.monus_scale _ _ _)))

/-- A proved integer value produces literal code equality, including zero,
negative integers and noncanonical signed pair representations. -/
theorem normalize_integer (a z : ZT n) (D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] ZT.eq a (ZT.ofNat D*z)) :
    Γ ⊢[PRAAx] normalize a D ≐ integerCode z := by
  have parts := scaled_parts a z D h
  have abs : Γ ⊢[PRAAx] zabs a ≐ D*zabs z :=
    (congrAdd (Prf.andE₁ parts) (Prf.andE₂ parts)).eqTrans (by unfold positivePart negativePart; ipra_ring)
  have g : Γ ⊢[PRAAx] divisor a D ≐ D :=
    (QuarticStep.congrGcd abs (.eqRefl _)).eqTrans (gcd_multiple _ D hD)
  have p := (congrAp2 quoF (Prf.andE₁ parts) g).eqTrans (quotient_multiple _ D hD)
  have q := (congrAp2 quoF (Prf.andE₂ parts) g).eqTrans (quotient_multiple _ D hD)
  have d : Γ ⊢[PRAAx] reducedDenominator a D ≐ one :=
    (congrAp2 quoF (by ipra_ring) g).eqTrans (quotient_multiple one D hD)
  exact congrPairT (congrPairT p q) ((congrPred d).eqTrans (pred_succ zero))

theorem integerCode_congr {a b : ZT n} (h : Γ ⊢[PRAAx] ZT.eq a b) :
    Γ ⊢[PRAAx] integerCode a ≐ integerCode b :=
  congrPairT (congrPairT (positivePart_congr h) (negativePart_congr h)) (.eqRefl _)

def normalizeF : PR 3 := PTm.toPR (normalize (⟨var 0,var 1⟩ : ZT 3) (var 2))

theorem normalize_at (p q D : PTm n) :
    Γ ⊢[PRAAx] ap3 normalizeF p q D ≐ normalize (⟨p,q⟩ : ZT n) D := by
  have h := toPR_eq (Γ := Γ) (normalize (⟨var 0,var 1⟩ : ZT 3) (var 2)) ![p,q,D]
  simpa only [normalizeF, ap3, subst_normalize, ZT.subst, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h

theorem normalization_program_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (ap3 normalizeF (var 0) (var 1) (var 2) ≐ normalize (⟨var 0,var 1⟩ : ZT 3) (var 2)) :=
  closeUniv 3 (normalize_at _ _ _)

theorem normalization_value_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le one (var 2) ⟶
        (le one (denominatorOf (normalize (⟨var 0,var 1⟩ : ZT 3) (var 2))) ⋏
          ZT.eq ((⟨var 0,var 1⟩ : ZT 3)*ZT.ofNat (denominatorOf (normalize (⟨var 0,var 1⟩ : ZT 3) (var 2))))
            (numeratorOf (normalize (⟨var 0,var 1⟩ : ZT 3) (var 2))*ZT.ofNat (var 2)))) :=
  closeUniv 3 (.impI (.andI
    (le_congr (.eqRefl _) (normalize_denominator _ _ Prf.hyp0).eqSymm (reduced_denominator_positive _ _ Prf.hyp0))
    (normalize_preserves_value _ _ Prf.hyp0)))

theorem integer_normalization_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (le one (var 4) ⟶
        ZT.eq (⟨var 0,var 1⟩ : ZT 5) (ZT.ofNat (var 4)*(⟨var 2,var 3⟩ : ZT 5)) ⟶
          (ap3 normalizeF (var 0) (var 1) (var 4) ≐ integerCode (⟨var 2,var 3⟩ : ZT 5))) :=
  closeUniv 5 (.impI (.impI ((normalize_at _ _ _).eqTrans (normalize_integer _ _ _ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalIntegerNormalization
