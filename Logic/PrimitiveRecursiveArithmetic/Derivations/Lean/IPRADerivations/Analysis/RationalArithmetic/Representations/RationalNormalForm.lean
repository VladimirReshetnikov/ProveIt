import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalIntegerNormalization

/-!
# Canonical guards for the actual gcd rational normalizer

The canonical scalar representation used by the Minkowski formula scheme
has a positive denominator, at most one nonzero signed numerator part, and
coprime absolute numerator and denominator.  Its raw code is the actual
pair constructor applied to those decoded fields.  This module proves these
guards for the normalizer, including the zero numerator case.  No ambient
integer or rational normalization theorem is used as an object derivation.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalNormalForm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalIntegerNormalization
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf rationalCode)
open LeanProofs.IPRA.Foundations.GapDecision (zabs)
open LeanProofs.IPRA.DiophantineNumberTheory
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.AnalyticNumberTheory.Order (gcd_pos_right)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem gcd_symmetric (a D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] gcd a D ≐ gcd D a := by
  have hd := positive_form hD
  have g := gcd_pos_right (a := a) hd
  have h := Foundations.ChineseRemainder.gcd_pos (B := a) hd
  have dg := gcd_dvd_at g
  have dh := gcd_dvd_at h
  exact le_antisymm
    (dvd_le' g (gcd_greatest' g (Prf.andE₂ dg) (Prf.andE₁ dg)) h)
    (dvd_le' h (gcd_greatest' h (Prf.andE₂ dh) (Prf.andE₁ dh)) g)

theorem reduced_parts_disjoint (a : ZT n) (D : PTm n) :
    Γ ⊢[PRAAx] ((reducedNumerator a D).pos ≐ zero) ⋎ ((reducedNumerator a D).neg ≐ zero) := by
  refine .orE (le_total a.pos a.neg) ?_ ?_
  · exact .orI₁ ((congrAp2 quoF Prf.hyp0 (.eqRefl _)).eqTrans (quo_zero _))
  · exact .orI₂ ((congrAp2 quoF Prf.hyp0 (.eqRefl _)).eqTrans (quo_zero _))

theorem reduced_absolute (a : ZT n) (D : PTm n) :
    Γ ⊢[PRAAx] zabs (reducedNumerator a D) ≐ quo (zabs a) (divisor a D) := by
  refine .orE (le_total a.pos a.neg) ?_ ?_
  · have p : (le a.pos a.neg :: Γ) ⊢[PRAAx] (reducedNumerator a D).pos ≐ zero :=
      (congrAp2 quoF Prf.hyp0 (.eqRefl _)).eqTrans (quo_zero _)
    have ab : (le a.pos a.neg :: Γ) ⊢[PRAAx] zabs a ≐ negativePart a :=
      (congrAdd Prf.hyp0 (.eqRefl _)).eqTrans (zero_add _)
    exact ((congrAdd ((congrMonus p (.eqRefl _)).eqTrans (zero_monus _))
        ((congrMonus (.eqRefl _) p).eqTrans (monus_zero _))).eqTrans (zero_add _)).eqTrans
      (congrAp2 quoF ab.eqSymm (.eqRefl _))
  · have q : (le a.neg a.pos :: Γ) ⊢[PRAAx] (reducedNumerator a D).neg ≐ zero :=
      (congrAp2 quoF Prf.hyp0 (.eqRefl _)).eqTrans (quo_zero _)
    have ab : (le a.neg a.pos :: Γ) ⊢[PRAAx] zabs a ≐ positivePart a :=
      (congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _)
    exact ((congrAdd ((congrMonus (.eqRefl _) q).eqTrans (monus_zero _))
        ((congrMonus q (.eqRefl _)).eqTrans (zero_monus _))).eqTrans (add_zero _)).eqTrans
      (congrAp2 quoF ab.eqSymm (.eqRefl _))

theorem reduced_coprime (a : ZT n) (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] gcd (zabs (reducedNumerator a D)) (reducedDenominator a D) ≐ one := by
  have comm := gcd_symmetric (zabs a) D hD
  have cp := coprime_quotients (c := zabs a) (positive_form hD)
  have cp' : Γ ⊢[PRAAx] gcd (reducedDenominator a D) (quo (zabs a) (divisor a D)) ≐ one :=
    (QuarticStep.congrGcd (congrAp2 quoF (.eqRefl _) comm)
      (congrAp2 quoF (.eqRefl _) comm)).eqTrans cp
  exact (gcd_symmetric _ _ (reduced_denominator_positive a D hD)).eqTrans
    ((QuarticStep.congrGcd (.eqRefl _) (reduced_absolute a D)).eqTrans cp')

/-- The raw scalar code is reconstructed from its decoded fields, its
signed numerator has no cancellation, and the decoded numerator and
positive denominator are coprime. -/
def wellFormed (c : PTm n) : Fm PTm n :=
  (c ≐ rationalCode (numeratorOf c) (denominatorOf c)) ⋏
    ((((numeratorOf c).pos ≐ zero) ⋎ ((numeratorOf c).neg ≐ zero)) ⋏
      (gcd (zabs (numeratorOf c)) (denominatorOf c) ≐ one))

@[simp] theorem subst_wellFormed {k : ℕ} (σ : Fin n → PTm k) (c : PTm n) :
    (wellFormed c).subst σ = wellFormed (Syn.subst σ c) := by
  have hg (u v : PTm n) : Syn.subst σ (gcd u v) = gcd (Syn.subst σ u) (Syn.subst σ v) := by
    simp only [gcd,subst_ex2,ConciseIPRA.PTm.subst_succ]
  simp only [wellFormed,Fm.subst_and,Fm.subst_or,Fm.subst_eq,hg,
    Foundations.GapDecision.subst_zabs,RationalSupMetric.subst_numeratorOf,
    RationalSupMetric.subst_denominatorOf,rationalCode,subst_pairT,PTm.subst_pred]
  simp only [RationalSupMetric.numeratorOf,ZT.subst,subst_fstT,subst_sndT,
    ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ]

theorem code_parts (a : ZT n) (D : PTm n) :
    Γ ⊢[PRAAx] ((numeratorOf (rationalCode a D)).pos ≐ a.pos) ⋏
      ((numeratorOf (rationalCode a D)).neg ≐ a.neg) :=
  .andI ((congrFst (fst_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _))

theorem code_reconstructed (a : ZT n) (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] rationalCode a D ≐
      rationalCode (numeratorOf (rationalCode a D)) (denominatorOf (rationalCode a D)) := by
  have parts := code_parts (Γ := Γ) a D
  exact (congrPairT (congrPairT (Prf.andE₁ parts) (Prf.andE₂ parts))
    (congrPred (RationalSupMetric.rationalCode_denominator a D hD))).eqSymm

theorem normalize_well_formed (a : ZT n) (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] wellFormed (normalize a D) := by
  have den := reduced_denominator_positive a D hD
  have parts := code_parts (Γ := Γ) (reducedNumerator a D) (reducedDenominator a D)
  have disjoint := reduced_parts_disjoint (Γ := Γ) a D
  have outdisjoint : Γ ⊢[PRAAx] ((numeratorOf (normalize a D)).pos ≐ zero) ⋎
      ((numeratorOf (normalize a D)).neg ≐ zero) := by
    refine .orE disjoint ?_ ?_
    · exact .orI₁ ((Prf.andE₁ parts.wk).eqTrans Prf.hyp0)
    · exact .orI₂ ((Prf.andE₂ parts.wk).eqTrans Prf.hyp0)
  have outabs : Γ ⊢[PRAAx] zabs (numeratorOf (normalize a D)) ≐ zabs (reducedNumerator a D) :=
    congrAdd (congrMonus (Prf.andE₁ parts) (Prf.andE₂ parts))
      (congrMonus (Prf.andE₂ parts) (Prf.andE₁ parts))
  exact .andI (code_reconstructed _ _ den) (.andI outdisjoint
    ((QuarticStep.congrGcd outabs (normalize_denominator a D hD)).eqTrans (reduced_coprime a D hD)))

theorem denominator_positive (c : PTm n) : Γ ⊢[PRAAx] le one (denominatorOf c) :=
  le_of_eq_add (d := sndT c) (by unfold denominatorOf; ipra_ring)

theorem unmixed_parts (a : ZT n)
    (h : Γ ⊢[PRAAx] (a.pos ≐ zero) ⋎ (a.neg ≐ zero)) :
    Γ ⊢[PRAAx] (positivePart a ≐ a.pos) ⋏ (negativePart a ≐ a.neg) := by
  refine .orE h ?_ ?_
  · exact .andI (((congrMonus Prf.hyp0 (.eqRefl _)).eqTrans (zero_monus _)).eqTrans Prf.hyp0.eqSymm)
      ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _))
  · exact .andI ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _))
      (((congrMonus Prf.hyp0 (.eqRefl _)).eqTrans (zero_monus _)).eqTrans Prf.hyp0.eqSymm)

theorem absolute_scale_right (a : ZT n) (D : PTm n) :
    Γ ⊢[PRAAx] zabs (a*ZT.ofNat D) ≐ zabs a*D := by
  have equal : ZT.toZ Γ (a*ZT.ofNat D) = ZT.toZ Γ (⟨D*a.pos,D*a.neg⟩ : ZT n) := by
    rw [ZT.toZ_mul,ZT.toZ_ofNat]
    simp only [ZT.toZ,Q.mk_mul,map_mul]
    ring
  exact ((Foundations.GapDecision.zabs_congr equal).eqTrans
    (Probability.MedianWeighted.ad_mul D a.pos a.neg)).eqTrans (mul_comm _ _)

/-- Cross equality and the two actual coprimality guards force equality of
the positive denominators.  Gauss's lemma is applied to natural absolute
numerators; zero numerators are included. -/
theorem denominators_unique (c d : PTm n)
    (hc : Γ ⊢[PRAAx] wellFormed c) (hd : Γ ⊢[PRAAx] wellFormed d)
    (h : Γ ⊢[PRAAx] ZT.eq (numeratorOf c*ZT.ofNat (denominatorOf d))
      (numeratorOf d*ZT.ofNat (denominatorOf c))) :
    Γ ⊢[PRAAx] denominatorOf c ≐ denominatorOf d := by
  have pc := positive_form (denominator_positive (Γ := Γ) c)
  have pd := positive_form (denominator_positive (Γ := Γ) d)
  have cross := (absolute_scale_right (Γ := Γ) (numeratorOf c) (denominatorOf d)).eqSymm.eqTrans
    ((Foundations.GapDecision.zabs_congr (ZT.toZ_eq h)).eqTrans
      (absolute_scale_right (numeratorOf d) (denominatorOf c)))
  have cp := (gcd_symmetric _ _ (denominator_positive (Γ := Γ) c)).eqSymm.eqTrans
    (Prf.andE₂ (Prf.andE₂ hc))
  have dp := (gcd_symmetric _ _ (denominator_positive (Γ := Γ) d)).eqSymm.eqTrans
    (Prf.andE₂ (Prf.andE₂ hd))
  have dc := gauss pc cp (dvd_congr cross.eqSymm (dvd_of_eq' pc (w := zabs (numeratorOf d)) (mul_comm _ _)))
  have dd := gauss pd dp (dvd_congr cross (dvd_of_eq' pd (w := zabs (numeratorOf c)) (mul_comm _ _)))
  exact le_antisymm (dvd_le' pc dc pd) (dvd_le' pd dd pc)

theorem positive_integer_cancel (D : PTm n) (a b : ZT n)
    (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] ZT.eq (a*ZT.ofNat D) (b*ZT.ofNat D)) : Γ ⊢[PRAAx] ZT.eq a b := by
  have value := ZT.toZ_eq h
  simp only [ZT.toZ_mul,ZT.toZ_ofNat] at value
  have scaled : Γ ⊢[PRAAx] D*(a.pos+b.neg) ≐ D*(b.pos+a.neg) := by
    apply deriveNat
    simp only [ZT.toZ] at value
    ipra_simps
    linear_combination value
  exact Combinatorics.BinomialIdentities.mul_cancel (positive_form hD) scaled

/-- Canonical codes of equal rational values are literally equal.  This is
usable for arbitrary arithmetic membership formulas, without an assumed
value-extensionality principle. -/
theorem well_formed_unique (c d : PTm n)
    (hc : Γ ⊢[PRAAx] wellFormed c) (hd : Γ ⊢[PRAAx] wellFormed d)
    (h : Γ ⊢[PRAAx] ZT.eq (numeratorOf c*ZT.ofNat (denominatorOf d))
      (numeratorOf d*ZT.ofNat (denominatorOf c))) : Γ ⊢[PRAAx] c ≐ d := by
  have den := denominators_unique c d hc hd h
  have cross : Γ ⊢[PRAAx] ZT.eq (numeratorOf c*ZT.ofNat (denominatorOf d))
      (numeratorOf d*ZT.ofNat (denominatorOf d)) := by
    apply ZT.derive
    have v := ZT.toZ_eq h
    have de := natEq den
    simp only [ZT.toZ_mul,ZT.toZ_ofNat] at v ⊢
    rw [de] at v
    exact v
  have num := positive_integer_cancel _ _ _ (denominator_positive d) cross
  have pc := unmixed_parts (numeratorOf c) (Prf.andE₁ (Prf.andE₂ hc))
  have pd := unmixed_parts (numeratorOf d) (Prf.andE₁ (Prf.andE₂ hd))
  have pe := (Prf.andE₁ pc).eqSymm.eqTrans ((positivePart_congr num).eqTrans (Prf.andE₁ pd))
  have ne := (Prf.andE₂ pc).eqSymm.eqTrans ((negativePart_congr num).eqTrans (Prf.andE₂ pd))
  exact (Prf.andE₁ hc).eqTrans ((congrPairT (congrPairT pe ne) (congrPred den)).eqTrans (Prf.andE₁ hd).eqSymm)

theorem zero_denominator (c : PTm n) (hc : Γ ⊢[PRAAx] wellFormed c)
    (hz : Γ ⊢[PRAAx] ZT.eq (numeratorOf c) (ZT.ofNat zero)) :
    Γ ⊢[PRAAx] denominatorOf c ≐ one := by
  have az : Γ ⊢[PRAAx] zabs (numeratorOf c) ≐ zero :=
    (Foundations.GapDecision.zabs_congr (ZT.toZ_eq hz)).eqTrans
      ((congrAdd (monus_self zero) (monus_self zero)).eqTrans (zero_add zero))
  have gzero : Γ ⊢[PRAAx] gcd zero (denominatorOf c) ≐ denominatorOf c :=
    (QuarticStep.congrGcd (mul_zero _).eqSymm (.eqRefl _)).eqTrans
      (gcd_multiple zero _ (denominator_positive c))
  exact gzero.eqSymm.eqTrans ((QuarticStep.congrGcd az.eqSymm (.eqRefl _)).eqTrans
    (Prf.andE₂ (Prf.andE₂ hc)))

theorem normalize_fixed_point (c : PTm n) (hc : Γ ⊢[PRAAx] wellFormed c) :
    Γ ⊢[PRAAx] normalize (numeratorOf c) (denominatorOf c) ≐ c := by
  apply well_formed_unique _ _ (normalize_well_formed _ _ (denominator_positive c)) hc
  apply ZT.derive
  exact (ZT.toZ_eq (normalize_preserves_value _ _ (denominator_positive (Γ := Γ) c))).symm

theorem normalize_idempotent (a : ZT n) (D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] normalize (numeratorOf (normalize a D)) (denominatorOf (normalize a D)) ≐ normalize a D :=
  normalize_fixed_point _ (normalize_well_formed a D hD)

theorem normalization_guard_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ wellFormed (normalize (⟨var 0,var 1⟩ : ZT 3) (var 2))) :=
  closeUniv 3 (.impI (normalize_well_formed _ _ Prf.hyp0))

theorem canonical_uniqueness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (wellFormed (var 0) ⟶ wellFormed (var 1) ⟶
      ZT.eq (numeratorOf (var 0)*ZT.ofNat (denominatorOf (var 1)))
        (numeratorOf (var 1)*ZT.ofNat (denominatorOf (var 0))) ⟶ (var 0 ≐ var 1)) :=
  closeUniv 2 (.impI (.impI (.impI (well_formed_unique _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem canonical_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (wellFormed (var 0) ⟶ ZT.eq (numeratorOf (var 0)) (ZT.ofNat zero) ⟶
      (denominatorOf (var 0) ≐ one)) :=
  closeUniv 1 (.impI (.impI (zero_denominator _ Prf.hyp1 Prf.hyp0)))

theorem normalization_idempotent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶
      (normalize (numeratorOf (normalize (⟨var 0,var 1⟩ : ZT 3) (var 2)))
        (denominatorOf (normalize (⟨var 0,var 1⟩ : ZT 3) (var 2))) ≐
          normalize (⟨var 0,var 1⟩ : ZT 3) (var 2))) :=
  closeUniv 3 (.impI (normalize_idempotent _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalNormalForm
