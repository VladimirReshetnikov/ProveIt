import IPRADerivations.Analysis.Polynomials.RootFinding.Deflation.GaussianRationalDeflation
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalReciprocal

/-!
# Actual reciprocal-Horner tails for runtime monic polynomials

The backwards coefficient fold computes the actual rational tail
sum_(i=1..N) c_i w^i. Its exact relation to the actual Horner evaluation
at z is derived from z*w=1. The input degree, lists, points, counters and
independently normalized scalar denominators remain internal. There is no
supplied polynomial, tail-evaluation or power-scaling identity.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianReciprocalHorner

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd qmul represents canonical qadd_canonical qmul_canonical qadd_represents qmul_represents
    represents_rescale represents_congr canonical_unique zero_represents positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qone_canonical qadd_congr qmul_congr rescale_to)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power power_zero power_succ)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (re im scale oneCode)
open LeanProofs.IPRA.Analysis.GaussianRootAlgebra
  (equal equal_of_values equal_re equal_im re_add im_add re_mul im_mul re_scale im_scale re_one im_one)
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-- Alternative numerators over the same scale are equal. Only the actual
positive decoded scalar denominators are canceled. -/
theorem numerator_unique (q a b E : PTm n)
    (ha : Γ ⊢[PRAAx] represents q a E) (hb : Γ ⊢[PRAAx] represents q b E) :
    Γ ⊢[PRAAx] equal a b := by
  refine .andI ?_ ?_
  · apply RationalNormalForm.positive_integer_cancel (denominatorOf (fstT q)) _ _ (RationalArgmin.denominator_positive _)
    apply ZT.derive
    have ea := ZT.toZ_eq (Prf.andE₁ ha)
    have eb := ZT.toZ_eq (Prf.andE₁ hb)
    simp only [RationalArithmetic.represents,ZT.toZ_mul,ZT.toZ_ofNat] at ea eb ⊢
    linear_combination ea-eb
  · apply RationalNormalForm.positive_integer_cancel (denominatorOf (sndT q)) _ _ (RationalArgmin.denominator_positive _)
    apply ZT.derive
    have ea := ZT.toZ_eq (Prf.andE₂ ha)
    have eb := ZT.toZ_eq (Prf.andE₂ hb)
    simp only [RationalArithmetic.represents,ZT.toZ_mul,ZT.toZ_ofNat] at ea eb ⊢
    linear_combination ea-eb

theorem qadd_zero_right (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx] qadd q qzero ≐ q := by
  have d := raw_den_positive (Γ := Γ) q
  have h := qadd_represents q qzero (rawGaussian q) ComplexLogarithmRemainder.zeroCode (rawDen q)
    d (raw_represents q) (zero_represents _)
  apply canonical_unique _ _ _ _ (qadd_canonical _ _) hq d (hrv := raw_represents q)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := h)
  apply equal_of_values <;> simp only [re_add,im_add,GaussianRootAlgebra.re_zero,GaussianRootAlgebra.im_zero] <;> ring

theorem qmul_one_right (q : PTm n) (hq : Γ ⊢[PRAAx] canonical q) : Γ ⊢[PRAAx] qmul q qone ≐ q := by
  have d := raw_den_positive (Γ := Γ) q
  have h := qmul_represents q qone (rawGaussian q) (scale (rawDen q) oneCode) (rawDen q) (rawDen q)
    d d (raw_represents q) (GaussianRationalReciprocal.qone_represents_scaled _)
  have target := represents_rescale q (rawGaussian q) (rawDen q) (rawDen q) (raw_represents (Γ := Γ) q)
  apply canonical_unique _ _ _ _ (qmul_canonical _ _) hq (positive_product _ _ d d) (hrv := target)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := h)
  apply equal_of_values <;> simp only [re_mul,im_mul,re_scale,im_scale,re_one,im_one] <;> ring

theorem qmul_associative_from_representations (q r s a b c E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hq : Γ ⊢[PRAAx] represents q a E)
    (hr : Γ ⊢[PRAAx] represents r b E) (hs : Γ ⊢[PRAAx] represents s c E) :
    Γ ⊢[PRAAx] qmul (qmul q r) s ≐ qmul q (qmul r s) := by
  have E2 := positive_product E E hE hE
  have E3 := positive_product (E*E) E E2 hE
  have lhs := qmul_represents _ _ _ _ _ _ E2 hE (qmul_represents _ _ _ _ _ _ hE hE hq hr) hs
  have rhs0 := qmul_represents _ _ _ _ _ _ hE E2 hq (qmul_represents _ _ _ _ _ _ hE hE hr hs)
  have rhs := represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_refl _) (mul_assoc E E E).eqSymm rhs0
  apply canonical_unique _ _ _ _ (qmul_canonical _ _) (qmul_canonical _ _) E3 (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply equal_of_values <;> simp only [re_mul,im_mul] <;> ring

theorem qmul_associative (q r s : PTm n) : Γ ⊢[PRAAx] qmul (qmul q r) s ≐ qmul q (qmul r s) := by
  let E := rawDen q*rawDen r*rawDen s
  have d : Γ ⊢[PRAAx] le one E := positive_product _ _ (positive_product _ _ (raw_den_positive q) (raw_den_positive r)) (raw_den_positive s)
  have hq := rescale_to q (rawGaussian q) (rawDen q) (rawDen r*rawDen s) E (raw_represents (Γ := Γ) q)
    (by unfold E; ipra_ring)
  have hr := rescale_to r (rawGaussian r) (rawDen r) (rawDen q*rawDen s) E (raw_represents (Γ := Γ) r)
    (by unfold E; ipra_ring)
  have hs := rescale_to s (rawGaussian s) (rawDen s) (rawDen q*rawDen r) E (raw_represents (Γ := Γ) s)
    (by unfold E; ipra_ring)
  exact qmul_associative_from_representations _ _ _ _ _ _ E d hq hr hs

/-- The one affine identity needed by the reciprocal tail recurrence. -/
theorem affine_inverse_from_representations (h z c t w a b d e f E : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hh : Γ ⊢[PRAAx] represents h a E)
    (hz : Γ ⊢[PRAAx] represents z b E) (hc : Γ ⊢[PRAAx] represents c d E)
    (ht : Γ ⊢[PRAAx] represents t e E) (hw : Γ ⊢[PRAAx] represents w f E)
    (hinverse : Γ ⊢[PRAAx] qmul z w ≐ qone) : Γ ⊢[PRAAx]
    qmul (qadd (qadd (qmul h z) c) t) w ≐ qadd h (qmul w (qadd t c)) := by
  have E2 := positive_product E E hE hE
  have E3 := positive_product (E*E) E E2 hE
  have inv := numerator_unique qone (ComplexLogarithmRemainder.mul b f) (scale (E*E) oneCode) (E*E)
    (represents_congr hinverse (GaussianRootAlgebra.equal_refl _) (.eqRefl _) (qmul_represents _ _ _ _ _ _ hE hE hz hw))
    (GaussianRationalReciprocal.qone_represents_scaled _)
  have ir := equal_re inv
  have ii := equal_im inv
  simp only [re_mul,im_mul,re_scale,im_scale,re_one,im_one] at ir ii
  have hzv := qmul_represents _ _ _ _ _ _ hE hE hh hz
  have c2 := represents_rescale c d E E hc
  have t2 := represents_rescale t e E E ht
  have sum := qadd_represents _ _ _ _ _ E2 (qadd_represents _ _ _ _ _ E2 hzv c2) t2
  have lhs := qmul_represents _ _ _ _ _ _ E2 hE sum hw
  have h3 := rescale_to h a E (E*E) ((E*E)*E) hh (by ipra_ring)
  have tw := qmul_represents _ _ _ _ _ _ hE hE hw (qadd_represents _ _ _ _ _ hE ht hc)
  have tw3 := represents_rescale _ _ (E*E) E tw
  have rhs := qadd_represents _ _ _ _ _ E3 h3 tw3
  apply canonical_unique _ _ _ _ (qmul_canonical _ _) (qadd_canonical _ _) E3 (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply equal_of_values
  · simp only [re_mul,im_mul,re_add,im_add,re_scale,im_scale]
    ipra_simps
    linear_combination ZT.toZ Γ (re a)*ir-ZT.toZ Γ (im a)*ii
  · simp only [re_mul,im_mul,re_add,im_add,re_scale,im_scale]
    ipra_simps
    linear_combination ZT.toZ Γ (im a)*ir+ZT.toZ Γ (re a)*ii

theorem affine_inverse (h z c t w : PTm n) (hinverse : Γ ⊢[PRAAx] qmul z w ≐ qone) : Γ ⊢[PRAAx]
    qmul (qadd (qadd (qmul h z) c) t) w ≐ qadd h (qmul w (qadd t c)) := by
  let E := rawDen h*GaussianRationalSyntheticDivision.remainingDen z c t w
  have d : Γ ⊢[PRAAx] le one E := positive_product _ _ (raw_den_positive h)
    (GaussianRationalSyntheticDivision.remaining_den_positive z c t w)
  have hh := rescale_to h (rawGaussian h) (rawDen h) (GaussianRationalSyntheticDivision.remainingDen z c t w) E (raw_represents (Γ := Γ) h) (.eqRefl _)
  have hz := rescale_to z (rawGaussian z) (rawDen z) (GaussianRationalSyntheticDivision.remainingDen h c t w) E (raw_represents (Γ := Γ) z)
    (by unfold E GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
  have hc := rescale_to c (rawGaussian c) (rawDen c) (GaussianRationalSyntheticDivision.remainingDen h z t w) E (raw_represents (Γ := Γ) c)
    (by unfold E GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
  have ht := rescale_to t (rawGaussian t) (rawDen t) (GaussianRationalSyntheticDivision.remainingDen h z c w) E (raw_represents (Γ := Γ) t)
    (by unfold E GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
  have hw := rescale_to w (rawGaussian w) (rawDen w) (GaussianRationalSyntheticDivision.remainingDen h z c t) E (raw_represents (Γ := Γ) w)
    (by unfold E GaussianRationalSyntheticDivision.remainingDen; ipra_ring)
  exact affine_inverse_from_representations _ _ _ _ _ _ _ _ _ _ E d hh hz hc ht hw hinverse

theorem qadd_commutative (a b : PTm n) : Γ ⊢[PRAAx] qadd a b ≐ qadd b a := by
  have d := positive_product _ _ (raw_den_positive (Γ := Γ) a) (raw_den_positive b)
  have ha := represents_rescale a (rawGaussian a) (rawDen a) (rawDen b) (raw_represents (Γ := Γ) a)
  have hb := rescale_to b (rawGaussian b) (rawDen b) (rawDen a) (rawDen a*rawDen b)
    (raw_represents (Γ := Γ) b) (mul_comm _ _)
  have lhs := qadd_represents _ _ _ _ _ d ha hb
  have rhs := qadd_represents _ _ _ _ _ d hb ha
  apply canonical_unique _ _ _ _ (qadd_canonical _ _) (qadd_canonical _ _) d (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply equal_of_values <;> simp only [re_add,im_add] <;> ring

theorem qsub_add_cancel (a b : PTm n) (ha : Γ ⊢[PRAAx] canonical a) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qsub (qadd a b) b ≐ a :=
  (GaussianRationalSyntheticDivision.qsub_congr (qadd_commutative a b) (.eqRefl _)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_sub_cancel b a ha)

/-! Actual backwards coefficient-Horner tail. -/

def tailData (C w N : PTm n) : PTm n := pairT C (pairT w N)
def tailStep : PTm 3 := qmul (fstT (sndT (var 2)))
  (qadd (var 1) (entry (fstT (var 2)) (monus (sndT (sndT (var 2))) (var 0))))
def tailF : PR 2 := rec2 (qzero : PTm 1) tailStep
def tail (C w N k : PTm n) : PTm n := ap2 tailF k (tailData C w N)

ipra_subst tailData
ipra_subst tail

theorem tail_zero (C w N : PTm n) : Γ ⊢[PRAAx] tail C w N zero ≐ qzero := by
  simpa only [tail,tailF,GaussianRationalHorner.subst_qzero] using rec2_zero (Γ := Γ) (qzero : PTm 1) tailStep (tailData C w N)

theorem tail_body_at (C w N k t : PTm n) : Γ ⊢[PRAAx]
    Syn.subst ![k,t,tailData C w N] tailStep ≐ qmul w (qadd t (entry C (monus N k))) := by
  have p := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (qmul (var 0) (qadd (var 1) (entry (var 2) (monus (var 3) (var 4)))) : PTm 5)
    (σ := ![fstT (sndT (tailData C w N)),t,fstT (tailData C w N),sndT (sndT (tailData C w N)),k])
    (σ' := ![w,t,C,N,k]) (fun i => by
      fin_cases i
      · exact (snd_pair _ _).fstE
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact (snd_pair _ _).sndE
      · exact .eqRefl _)
  simpa only [tailStep,GaussianRationalHorner.subst_qmul,GaussianRationalHorner.subst_qadd,subst_entry,
    PTm.subst_monus,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using p

theorem tail_succ (C w N k : PTm n) : Γ ⊢[PRAAx]
    tail C w N (succ k) ≐ qmul w (qadd (tail C w N k) (entry C (monus N k))) :=
  (rec2_succ (qzero : PTm 1) tailStep k (tailData C w N)).eqTrans (tail_body_at C w N k _)

theorem tail_canonical (C w N k : PTm n) : Γ ⊢[PRAAx] canonical (tail C w N k) := by
  refine .orE (zero_or_succ k) ?_ ?_
  · exact GaussianRationalHorner.canonical_congr
      ((congrAp2 tailF Prf.hyp0 (.eqRefl _)).eqTrans (tail_zero C w N))
      GaussianRationalSyntheticDivision.qzero_canonical
  · exact GaussianRationalHorner.canonical_congr
      ((congrAp2 tailF Prf.hyp0 (.eqRefl _)).eqTrans (tail_succ C w N _)) (qmul_canonical _ _)

/-! The actual polynomial's value times a reciprocal power is split into
its remaining Horner prefix plus the computed backwards tail. -/

def prefixLaw (C z w N k : PTm n) : Fm PTm n := le k N ⟶
  qmul (GaussianRationalHorner.evaluate C z) (power w k) ≐
    qadd (GaussianRationalHorner.horner C z (succ (monus N k))) (tail C w N k)

ipra_subst prefixLaw

theorem prefix_zero (C z w N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    qmul (GaussianRationalHorner.evaluate C z) (power w zero) ≐
      qadd (GaussianRationalHorner.horner C z (succ (monus N zero))) (tail C w N zero) := by
  have can : Γ ⊢[PRAAx] canonical (GaussianRationalHorner.evaluate C z) := GaussianRationalHorner.horner_canonical _ _ _
  have lhs : Γ ⊢[PRAAx] qmul (GaussianRationalHorner.evaluate C z) (power w zero) ≐ GaussianRationalHorner.evaluate C z :=
    (qmul_congr (.eqRefl _) (power_zero w)).eqTrans (qmul_one_right _ can)
  have h : Γ ⊢[PRAAx] GaussianRationalHorner.horner C z (succ (monus N zero)) ≐ GaussianRationalHorner.evaluate C z :=
    congrAp3 GaussianRationalHorner.hornerF ((congrSucc (monus_zero N)).eqTrans hC.eqSymm) (.eqRefl _) (.eqRefl _)
  exact lhs.eqTrans ((qadd_congr h (tail_zero C w N)).eqTrans (qadd_zero_right _ can)).eqSymm

theorem prefix_step (C z w N k : PTm n) (hk : Γ ⊢[PRAAx] lt k N)
    (hinverse : Γ ⊢[PRAAx] qmul z w ≐ qone)
    (ih : Γ ⊢[PRAAx] qmul (GaussianRationalHorner.evaluate C z) (power w k) ≐
      qadd (GaussianRationalHorner.horner C z (succ (monus N k))) (tail C w N k)) : Γ ⊢[PRAAx]
    qmul (GaussianRationalHorner.evaluate C z) (power w (succ k)) ≐
      qadd (GaussianRationalHorner.horner C z (succ (monus N (succ k)))) (tail C w N (succ k)) := by
  have idx : Γ ⊢[PRAAx] GaussianRationalHorner.horner C z (monus N k) ≐
      GaussianRationalHorner.horner C z (succ (monus N (succ k))) :=
    congrAp3 GaussianRationalHorner.hornerF (GaussianRationalDeflation.remaining_step N k hk) (.eqRefl _) (.eqRefl _)
  exact (qmul_congr (.eqRefl _) (power_succ w k)).eqTrans
    ((qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr ih (.eqRefl _)).eqTrans
        ((qmul_congr (qadd_congr (GaussianRationalHorner.horner_succ C z (monus N k)) (.eqRefl _)) (.eqRefl _)).eqTrans
          ((affine_inverse (GaussianRationalHorner.horner C z (monus N k)) z (entry C (monus N k))
            (tail C w N k) w hinverse).eqTrans
              (qadd_congr idx (tail_succ C w N k).eqSymm)))))

theorem prefix_identity (C z w N k : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hinverse : Γ ⊢[PRAAx] qmul z w ≐ qone) (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx]
    qmul (GaussianRationalHorner.evaluate C z) (power w k) ≐
      qadd (GaussianRationalHorner.horner C z (succ (monus N k))) (tail C w N k) := by
  have invShift : Γ.map Fm.shift ⊢[PRAAx] qmul (Syn.shift z) (Syn.shift w) ≐ qone := by
    simpa only [Fm.shift,Fm.subst_eq,GaussianRationalHorner.subst_qmul,GaussianRationalSyntheticDivision.subst_qone,Syn.shift] using hinverse.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift C) (Syn.shift z) (Syn.shift w) (Syn.shift N) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_prefixLaw]
    · exact .impI (prefix_zero C z w N hC.wk)
    · refine .impI ?_
      let I := prefixLaw (Syn.shift C) (Syn.shift z) (Syn.shift w) (Syn.shift N) (var 0)
      let Δ := le (succ (var 0)) (Syn.shift N) :: I :: Γ.map Fm.shift
      exact prefix_step _ _ _ _ _ Prf.hyp0 invShift.wk.wk (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have rule : Γ ⊢[PRAAx] prefixLaw C z w N k := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE k all
  exact .impE rule hk

/-- Exact reciprocal-Horner identity for every runtime monic degree,
including degree zero. No completed-real or generic-polynomial axiom is used. -/
theorem monic_identity (C z w N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hMonic : Γ ⊢[PRAAx] entry C zero ≐ qone) (hinverse : Γ ⊢[PRAAx] qmul z w ≐ qone) : Γ ⊢[PRAAx]
    qmul (GaussianRationalHorner.evaluate C z) (power w N) ≐ qadd qone (tail C w N N) := by
  have head : Γ ⊢[PRAAx] GaussianRationalHorner.horner C z (succ (monus N N)) ≐ qone :=
    (congrAp3 GaussianRationalHorner.hornerF (congrSucc (monus_self N)) (.eqRefl _) (.eqRefl _)).eqTrans
      ((GaussianRationalSyntheticDivision.first_prefix C z).eqTrans
        ((qadd_congr (.eqRefl _) hMonic).eqTrans (GaussianRationalSyntheticDivision.qzero_add qone qone_canonical)))
  exact (prefix_identity C z w N N hC hinverse (le_refl _)).eqTrans (qadd_congr head (.eqRefl _))

theorem isolated_one (C z w N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hMonic : Γ ⊢[PRAAx] entry C zero ≐ qone) (hinverse : Γ ⊢[PRAAx] qmul z w ≐ qone) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qsub (qmul (GaussianRationalHorner.evaluate C z) (power w N)) (tail C w N N) ≐ qone :=
  (GaussianRationalSyntheticDivision.qsub_congr (monic_identity C z w N hC hMonic hinverse) (.eqRefl _)).eqTrans
    (qsub_add_cancel qone _ qone_canonical)

/-- The actual reciprocal producer supplies its own inverse equation; only
the legitimate nonzero squared-norm guard is a hypothesis. -/
theorem actual_reciprocal_identity (C z N : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hMonic : Γ ⊢[PRAAx] entry C zero ≐ qone)
    (hz : Γ ⊢[PRAAx] le one (GaussianRationalReciprocal.normNumerator z)) : Γ ⊢[PRAAx]
    qmul (GaussianRationalHorner.evaluate C z) (power (GaussianRationalReciprocal.reciprocal z) N) ≐
      qadd qone (tail C (GaussianRationalReciprocal.reciprocal z) N N) :=
  monic_identity _ _ _ _ hC hMonic (GaussianRationalReciprocal.reciprocal_identity z hz)

def tailProgramF : PR 4 := PTm.toPR (tail (var 0) (var 1) (var 2) (var 3))
theorem tail_program_at (C w N k : PTm n) : Γ ⊢[PRAAx]
    PTm.app tailProgramF ![C,w,N,k] ≐ tail C w N k := by
  simpa [tailProgramF] using toPR_eq (Γ := Γ) (tail (var 0) (var 1) (var 2) (var 3) : PTm 4) ![C,w,N,k]

theorem reciprocal_horner_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((length (var 0) ≐ succ (var 3)) ⟶ (entry (var 0) zero ≐ qone) ⟶ (qmul (var 1) (var 2) ≐ qone) ⟶
      (qmul (GaussianRationalHorner.evaluate (var 0) (var 1)) (power (var 2) (var 3)) ≐
        qadd qone (tail (var 0) (var 2) (var 3) (var 3)))) :=
  closeUniv 4 (.impI (.impI (.impI (monic_identity _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem actual_reciprocal_horner_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((length (var 0) ≐ succ (var 2)) ⟶ (entry (var 0) zero ≐ qone) ⟶
      le one (GaussianRationalReciprocal.normNumerator (var 1)) ⟶
      (qmul (GaussianRationalHorner.evaluate (var 0) (var 1)) (power (GaussianRationalReciprocal.reciprocal (var 1)) (var 2)) ≐
        qadd qone (tail (var 0) (GaussianRationalReciprocal.reciprocal (var 1)) (var 2) (var 2)))) :=
  closeUniv 3 (.impI (.impI (.impI (actual_reciprocal_identity _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem reciprocal_tail_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((PTm.app tailProgramF ![var 0,var 1,var 2,var 3] ≐ tail (var 0) (var 1) (var 2) (var 3)) ⋏
      canonical (tail (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.andI (tail_program_at _ _ _ _) (tail_canonical _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianReciprocalHorner
