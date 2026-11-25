import IPRADerivations.Analysis.RationalOriginalSpanMembership
import IPRADerivations.Analysis.RationalSuperellipticSubspace
import IPRADerivations.Foundations.FiniteCoverAssignment
import IPRADerivations.Core.CongruenceTactic

/-!
# First-cover counting for original rational superelliptic points

Each source family entry is a matrix of original rational rows. The actual
candidate test evaluates the stored weighted monomials on the original
point and tests its original rational span membership. The groups retain
the original point codes in increasing index order.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalSuperellipticCover

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianWeightedMonomialBasis (count)
open RationalSuperellipticNormDegree (d pointPowers point_power_at subst_pointPowers)
open RationalSuperellipticSubspace (curveInput curvePoints properSpan pointMembership)
open RationalRowSpanGaussianEmbedding (hasCoefficients subst_hasCoefficients)
open RationalWeightedMonomialEvaluation (vector)
open RationalCurvePointsGaussianEmbedding (distinct distinctFrom distinct_at subst_distinct)
open RationalArgmin (rationalEq rationalEq_congr)
open GaussianRationalFiberGrouping (abscissa ordinate subst_abscissa subst_ordinate)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Foundations.FiniteCoverAssignment
  (hasCover cover groupBounds group_length index_bound indices_increasing group_lookup group_test)
open ConciseIPRA.PTm (zero app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def candidate (m e L D g v : PTm n) : PTm n := RationalOriginalSpanMembership.test
  (entry D g) (length (entry D g)) (count m e L) (vector m e L (fstT v) (sndT v))

def data (m e L D : PTm n) : PTm n := pairT m (pairT e (pairT L D))

def testBody : PTm 3 := eqb (candidate (fstT (var 2)) (fstT (sndT (var 2)))
  (fstT (sndT (sndT (var 2)))) (sndT (sndT (sndT (var 2)))) (var 0) (var 1)) one

def family (m e L D : PTm n) : Fm PTm n := .all (lt (var 0) (length (Syn.shift D)) ⟶
  properSpan (entry (Syn.shift D) (var 0)) (length (entry (Syn.shift D) (var 0)))
    (count (Syn.shift m) (Syn.shift e) (Syn.shift L)))

def coveredAt (m e L D v : PTm n) : Fm PTm n := .ex (lt (var 0) (length (Syn.shift D)) ⋏
  hasCoefficients (entry (Syn.shift D) (var 0)) (length (entry (Syn.shift D) (var 0)))
    (count (Syn.shift m) (Syn.shift e) (Syn.shift L))
    (vector (Syn.shift m) (Syn.shift e) (Syn.shift L) (fstT (Syn.shift v)) (sndT (Syn.shift v))))

def covered (m e L P D : PTm n) : Fm PTm n := .all (lt (var 0) (length (Syn.shift P)) ⟶
  coveredAt (Syn.shift m) (Syn.shift e) (Syn.shift L) (Syn.shift D) (entry (Syn.shift P) (var 0)))

def group (m e L P D g : PTm n) : PTm n :=
  Foundations.FiniteCoverAssignment.group testBody P (length D) (data m e L D) g

@[simp] theorem subst_candidate {q : ℕ} (σ : Fin n → PTm q) (m e L D g v : PTm n) :
    Syn.subst σ (candidate m e L D g v) = candidate (Syn.subst σ m) (Syn.subst σ e) (Syn.subst σ L)
      (Syn.subst σ D) (Syn.subst σ g) (Syn.subst σ v) := by simp [candidate]

@[simp] theorem subst_data {q : ℕ} (σ : Fin n → PTm q) (m e L D : PTm n) :
    Syn.subst σ (data m e L D) = data (Syn.subst σ m) (Syn.subst σ e) (Syn.subst σ L) (Syn.subst σ D) := by simp [data]

@[simp] theorem subst_family {q : ℕ} (σ : Fin n → PTm q) (m e L D : PTm n) :
    (family m e L D).subst σ = family (Syn.subst σ m) (Syn.subst σ e) (Syn.subst σ L) (Syn.subst σ D) := by
  simp [family,Syn.subst_shift,Syn.shift_subst]

@[simp] theorem subst_coveredAt {q : ℕ} (σ : Fin n → PTm q) (m e L D v : PTm n) :
    (coveredAt m e L D v).subst σ = coveredAt (Syn.subst σ m) (Syn.subst σ e) (Syn.subst σ L)
      (Syn.subst σ D) (Syn.subst σ v) := by simp [coveredAt,Syn.subst_shift,Syn.shift_subst]

@[simp] theorem subst_covered {q : ℕ} (σ : Fin n → PTm q) (m e L P D : PTm n) :
    (covered m e L P D).subst σ = covered (Syn.subst σ m) (Syn.subst σ e) (Syn.subst σ L)
      (Syn.subst σ P) (Syn.subst σ D) := by simp [covered,Syn.subst_shift,Syn.shift_subst]

@[simp] theorem subst_group {q : ℕ} (σ : Fin n → PTm q) (m e L P D g : PTm n) :
    Syn.subst σ (group m e L P D g) = group (Syn.subst σ m) (Syn.subst σ e) (Syn.subst σ L)
      (Syn.subst σ P) (Syn.subst σ D) (Syn.subst σ g) := by simp [group]

private theorem candidate_congr {m m' e e' L L' D D' : PTm n} (g v : PTm n)
    (hm : Γ ⊢[PRAAx] m ≐ m') (he : Γ ⊢[PRAAx] e ≐ e') (hL : Γ ⊢[PRAAx] L ≐ L') (hD : Γ ⊢[PRAAx] D ≐ D') :
    Γ ⊢[PRAAx] candidate m e L D g v ≐ candidate m' e' L' D' g v := by
  ipra_congr (candidate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with
    [hm, he, hL, hD, .eqRefl g, .eqRefl v] using [GaussianAnnihilatorPolynomial.val_five]

theorem test_body_at (m e L D g v : PTm n) : Γ ⊢[PRAAx]
    inst3 testBody g v (data m e L D) ≐ eqb (candidate m e L D g v) one := by
  have firstTail := snd_pair (Γ := Γ) m (pairT e (pairT L D))
  have lastTail := (congrSnd firstTail).eqTrans (snd_pair e (pairT L D))
  have h := candidate_congr g v (fst_pair m (pairT e (pairT L D)))
    ((congrFst firstTail).eqTrans (fst_pair _ _)) ((congrFst lastTail).eqTrans (fst_pair _ _))
    ((congrSnd lastTail).eqTrans (snd_pair _ _))
  simpa only [testBody,inst3,subst_eqb,subst_candidate,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,one,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero,Matrix.head_cons,Matrix.tail_cons,data] using
    Foundations.FiniteFiberGrouping.eqb_congr h (.eqRefl one)

theorem family_at (m e L D g : PTm n) (h : Γ ⊢[PRAAx] family m e L D) (hg : Γ ⊢[PRAAx] lt g (length D)) :
    Γ ⊢[PRAAx] properSpan (entry D g) (length (entry D g)) (count m e L) := by
  have rule : Γ ⊢[PRAAx] lt g (length D) ⟶ properSpan (entry D g) (length (entry D g)) (count m e L) := by
    simpa [family] using h.allE g
  exact .impE rule hg

theorem candidate_complete (m e L D g v : PTm n)
    (h : Γ ⊢[PRAAx] hasCoefficients (entry D g) (length (entry D g)) (count m e L) (vector m e L (fstT v) (sndT v))) :
    Γ ⊢[PRAAx] inst3 testBody g v (data m e L D) ≐ one :=
  (test_body_at m e L D g v).eqTrans (eqb_of_eq (RationalOriginalSpanMembership.test_complete _ _ _ _ h))

theorem candidate_sound (m e L D g v : PTm n) (h : Γ ⊢[PRAAx] neg (inst3 testBody g v (data m e L D) ≐ zero)) :
    Γ ⊢[PRAAx] hasCoefficients (entry D g) (length (entry D g)) (count m e L) (vector m e L (fstT v) (sndT v)) := by
  have bit := Foundations.FiniteFiberGrouping.equality_of_nonzero_eqb
    (.impI (.impE h.wk ((test_body_at m e L D g v).wk.eqTrans Prf.hyp0)))
  exact (RationalOriginalSpanMembership.test_iff _ _ _ _).iffMp bit

theorem coveredAt_reflected (m e L D v : PTm n) (h : Γ ⊢[PRAAx] coveredAt m e L D v) :
    Γ ⊢[PRAAx] hasCover testBody (length D) v (data m e L D) := by
  refine .exE h ?_
  let Δ := (lt (var 0) (length (Syn.shift D)) ⋏
    hasCoefficients (entry (Syn.shift D) (var 0)) (length (entry (Syn.shift D) (var 0)))
      (count (Syn.shift m) (Syn.shift e) (Syn.shift L))
      (vector (Syn.shift m) (Syn.shift e) (Syn.shift L) (fstT (Syn.shift v)) (sndT (Syn.shift v)))) :: Γ.map Fm.shift
  have hit := candidate_complete (Γ := Δ) (Syn.shift m) (Syn.shift e) (Syn.shift L) (Syn.shift D) (var 0) (Syn.shift v)
    (.andE₂ Prf.hyp0)
  have out : Δ ⊢[PRAAx] hasCover testBody (length (Syn.shift D)) (Syn.shift v)
      (data (Syn.shift m) (Syn.shift e) (Syn.shift L) (Syn.shift D)) := by
    refine .exI (var 0) ?_
    have nonzero : Δ ⊢[PRAAx] neg (inst3 testBody (var 0) (Syn.shift v)
        (data (Syn.shift m) (Syn.shift e) (Syn.shift L) (Syn.shift D)) ≐ zero) :=
      .impI (succ_ne_zero (hit.wk.eqSymm.eqTrans Prf.hyp0))
    simpa only [hasCover,Fm.subst_and,subst_lt,subst_neg,Fm.subst_eq,subst_inst3,Syn.subst_var,Syn.inst_zero,
      Syn.subst_inst_shift,ConciseIPRA.PTm.subst_zero] using Prf.andI (.andE₁ (Prf.hyp0 : Δ ⊢[PRAAx] _)) nonzero
  simpa only [Δ,Fm.shift,Foundations.FiniteCoverAssignment.subst_hasCover,subst_length,subst_data,Syn.shift] using out

theorem covered_at (m e L P D i : PTm n) (h : Γ ⊢[PRAAx] covered m e L P D) (hi : Γ ⊢[PRAAx] lt i (length P)) :
    Γ ⊢[PRAAx] coveredAt m e L D (entry P i) := by
  have rule : Γ ⊢[PRAAx] lt i (length P) ⟶ coveredAt m e L D (entry P i) := by simpa [covered] using h.allE i
  exact .impE rule hi

theorem generic_cover (m e L P D : PTm n) (h : Γ ⊢[PRAAx] covered m e L P D) : Γ ⊢[PRAAx]
    cover testBody P (length D) (data m e L D) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] covered (Syn.shift m) (Syn.shift e) (Syn.shift L) (Syn.shift P) (Syn.shift D) := by
    simpa only [Fm.shift,subst_covered,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift P)) :: Γ.map Fm.shift
  have hit := coveredAt_reflected (Γ := Δ) (Syn.shift m) (Syn.shift e) (Syn.shift L) (Syn.shift D)
    (entry (Syn.shift P) (var 0)) (covered_at _ _ _ _ _ _ hs.wk Prf.hyp0)
  simpa only [Δ,Syn.shift,subst_length,subst_data] using hit

def first (m e L P D i : PTm n) : PTm n :=
  Foundations.FiniteCoverAssignment.label testBody P (length D) (data m e L D) i

theorem first_correct (m e L P D i : PTm n) (h : Γ ⊢[PRAAx] covered m e L P D)
    (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx]
    lt (first m e L P D i) (length D) ⋏ hasCoefficients (entry D (first m e L P D i))
      (length (entry D (first m e L P D i))) (count m e L) (vector m e L (abscissa P i) (ordinate P i)) := by
  have hit := Foundations.FiniteCoverAssignment.cover_label testBody P (length D) (data m e L D) i
    (generic_cover _ _ _ _ _ h) hi
  exact .andI (.andE₁ hit) (candidate_sound _ _ _ _ (first m e L P D i) (entry P i) (.andE₂ hit))

theorem first_least (m e L P D i g : PTm n)
    (h : Γ ⊢[PRAAx] hasCoefficients (entry D g) (length (entry D g)) (count m e L)
      (vector m e L (abscissa P i) (ordinate P i))) : Γ ⊢[PRAAx] le (first m e L P D i) g := by
  have hit := candidate_complete m e L D g (entry P i) h
  exact Foundations.FiniteCoverAssignment.assigned_least testBody (length D) (entry P i) (data m e L D) g
    (.impI (succ_ne_zero (hit.wk.eqSymm.eqTrans Prf.hyp0)))

theorem group_membership (m e L P D g : PTm n) (h : Γ ⊢[PRAAx] covered m e L P D) : Γ ⊢[PRAAx]
    pointMembership m e L (group m e L P D g) (entry D g) (length (entry D g)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] covered (Syn.shift m) (Syn.shift e) (Syn.shift L) (Syn.shift P) (Syn.shift D) := by
    simpa only [Fm.shift,subst_covered,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let payload := data (Syn.shift m) (Syn.shift e) (Syn.shift L) (Syn.shift D)
  let G := group (Syn.shift m) (Syn.shift e) (Syn.shift L) (Syn.shift P) (Syn.shift D) (Syn.shift g)
  let Δ := lt (var 0) (length G) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 0) (length G) := Prf.hyp0
  have hb := lt_congr (.eqRefl (var 0)) (group_length testBody (Syn.shift P) (length (Syn.shift D)) payload (Syn.shift g)) hi
  have hit := group_test testBody (Syn.shift P) (length (Syn.shift D)) payload (Syn.shift g) (var 0)
    (generic_cover _ _ _ _ _ hs.wk) hb
  simpa only [Δ,G,payload,Syn.shift,subst_entry,subst_length,subst_group,abscissa,ordinate] using
    candidate_sound (Syn.shift m) (Syn.shift e) (Syn.shift L) (Syn.shift D) (Syn.shift g) (entry G (var 0)) hit

private theorem group_power_at (f m e L P D g i : PTm n) (h : Γ ⊢[PRAAx] pointPowers f m P)
    (hi : Γ ⊢[PRAAx] lt i (length (group m e L P D g))) : Γ ⊢[PRAAx]
    rationalEq (RationalScalarPowerGaussianEmbedding.power (ordinate (group m e L P D g) i) m)
      (RationalPolynomialGaussianEmbedding.evaluate f (abscissa (group m e L P D g) i)) := by
  let payload := data m e L D
  have hb := lt_congr (.eqRefl i) (group_length testBody P (length D) payload g) hi
  have eq := group_lookup testBody P (length D) payload g i hb
  have original := point_power_at f m P _ h (index_bound testBody P (length D) payload g i hb)
  have py := congrAp2 RationalScalarPowerGaussianEmbedding.powerF (.eqRefl m) (congrSnd eq)
  have px := congrAp3 RationalPolynomialGaussianEmbedding.hornerF (.eqRefl (length f)) (.eqRefl f) (congrFst eq)
  exact rationalEq_congr py.eqSymm px.eqSymm original

theorem group_powers (f m e L P D g : PTm n) (h : Γ ⊢[PRAAx] pointPowers f m P) :
    Γ ⊢[PRAAx] pointPowers f m (group m e L P D g) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointPowers (Syn.shift f) (Syn.shift m) (Syn.shift P) := by
    simpa only [Fm.shift,Syn.shift,subst_pointPowers] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_group,RationalScalarPowerGaussianEmbedding.subst_power,
    RationalPolynomialGaussianEmbedding.subst_evaluate,subst_abscissa,subst_ordinate] using
    group_power_at (Syn.shift f) (Syn.shift m) (Syn.shift e) (Syn.shift L) (Syn.shift P)
      (Syn.shift D) (Syn.shift g) (var 0) hs.wk Prf.hyp0

private theorem group_distinct_at (m e L P D g i j : PTm n) (h : Γ ⊢[PRAAx] distinct P)
    (hi : Γ ⊢[PRAAx] lt i (length (group m e L P D g)))
    (hj : Γ ⊢[PRAAx] lt j (length (group m e L P D g))) (hij : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx]
    neg (rationalEq (abscissa (group m e L P D g) j) (abscissa (group m e L P D g) i) ⋏
      rationalEq (ordinate (group m e L P D g) j) (ordinate (group m e L P D g) i)) := by
  let payload := data m e L D
  let I := Foundations.FiniteCoverAssignment.indices testBody P (length D) payload g
  have size := group_length (Γ := Γ) testBody P (length D) payload g
  have bi := lt_congr (.eqRefl i) size hi
  have bj := lt_congr (.eqRefl j) size hj
  have ei := group_lookup testBody P (length D) payload g i bi
  have ej := group_lookup testBody P (length D) payload g j bj
  have original := distinct_at P (entry I i) (entry I j) h
    (index_bound testBody P (length D) payload g i bi) (index_bound testBody P (length D) payload g j bj)
    (indices_increasing testBody P (length D) payload g i j hij bj)
  exact .impI (.impE original.wk (.andI
    (rationalEq_congr (congrFst ej.wk) (congrFst ei.wk) (.andE₁ Prf.hyp0))
    (rationalEq_congr (congrSnd ej.wk) (congrSnd ei.wk) (.andE₂ Prf.hyp0))))

theorem group_distinct (m e L P D g : PTm n) (h : Γ ⊢[PRAAx] distinct P) :
    Γ ⊢[PRAAx] distinct (group m e L P D g) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] distinct (Syn.shift P) := by
    simpa only [Fm.shift,Syn.shift,subst_distinct] using h.shift
  refine .allI (.impI ?_)
  let G := group (Syn.shift m) (Syn.shift e) (Syn.shift L) (Syn.shift P) (Syn.shift D) (Syn.shift g)
  let Δ := lt (var 0) (length G) :: Γ.map Fm.shift
  have hg : Δ ⊢[PRAAx] lt (var 0) (length G) := Prf.hyp0
  have inner : Δ ⊢[PRAAx] distinctFrom G (var 0) := by
    refine .allI (.impI (.impI ?_))
    let i := Syn.shift (var 0 : PTm (n + 1))
    let G' := group (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift e)) (Syn.shift (Syn.shift L))
      (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift g))
    have hgs : Δ.map Fm.shift ⊢[PRAAx] lt i (length G') := by
      simpa only [i,G,G',Fm.shift,subst_lt,subst_length,subst_group,Syn.shift] using hg.shift
    have hDs : Δ.map Fm.shift ⊢[PRAAx] distinct (Syn.shift (Syn.shift P)) := by
      simpa only [Fm.shift,subst_distinct,Syn.shift] using (hs.wk : Δ ⊢[PRAAx] distinct (Syn.shift P)).shift
    simpa only [i,G,G',Syn.shift,subst_group,subst_abscissa,subst_ordinate,RationalArgmin.subst_rationalEq,
      Fm.subst_and] using group_distinct_at (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift e)) (Syn.shift (Syn.shift L))
      (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift g)) i (var 0)
      hDs.wk.wk hgs.wk.wk Prf.hyp1 Prf.hyp0
  simpa only [Δ,G,Syn.shift,subst_group,subst_length] using inner

@[simp] theorem subst_curveInput {q : ℕ} (σ : Fin n → PTm q) (f m c : PTm n) :
    (curveInput f m c).subst σ = curveInput (Syn.subst σ f) (Syn.subst σ m) (Syn.subst σ c) := by
  have hg (u v : PTm n) : Syn.subst σ (gcd u v) = gcd (Syn.subst σ u) (Syn.subst σ v) := by
    simp only [gcd,subst_ex2,ConciseIPRA.PTm.subst_succ]
  simp [curveInput,d,hg]

theorem group_bound (f m c L P D g : PTm n) (hf : Γ ⊢[PRAAx] curveInput f m c)
    (hPoints : Γ ⊢[PRAAx] curvePoints f m P) (hFamily : Γ ⊢[PRAAx] family m (d f c) L D)
    (hCover : Γ ⊢[PRAAx] covered m (d f c) L P D) (hg : Γ ⊢[PRAAx] lt g (length D)) : Γ ⊢[PRAAx]
    le (length (group m (d f c) L P D g)) L :=
  RationalSuperellipticSubspace.point_bound f m c L (group m (d f c) L P D g) (entry D g) (length (entry D g)) hf
    (family_at _ _ _ _ _ hFamily hg) (.andI (group_distinct _ _ _ _ _ _ (.andE₁ hPoints)) (group_powers _ _ _ _ _ _ _ (.andE₂ hPoints)))
    (group_membership _ _ _ _ _ _ hCover)

theorem group_bounds (f m c L P D : PTm n) (hf : Γ ⊢[PRAAx] curveInput f m c)
    (hPoints : Γ ⊢[PRAAx] curvePoints f m P) (hFamily : Γ ⊢[PRAAx] family m (d f c) L D)
    (hCover : Γ ⊢[PRAAx] covered m (d f c) L P D) : Γ ⊢[PRAAx]
    groupBounds testBody P (length D) (data m (d f c) L D) L := by
  have fs : Γ.map Fm.shift ⊢[PRAAx] curveInput (Syn.shift f) (Syn.shift m) (Syn.shift c) := by
    simpa only [Fm.shift,Syn.shift,subst_curveInput] using hf.shift
  have ps : Γ.map Fm.shift ⊢[PRAAx] curvePoints (Syn.shift f) (Syn.shift m) (Syn.shift P) := by
    simpa [curvePoints,Fm.shift,Syn.shift] using hPoints.shift
  have fam : Γ.map Fm.shift ⊢[PRAAx] family (Syn.shift m) (d (Syn.shift f) (Syn.shift c)) (Syn.shift L) (Syn.shift D) := by
    simpa [d,Fm.shift,Syn.shift] using hFamily.shift
  have cov : Γ.map Fm.shift ⊢[PRAAx] covered (Syn.shift m) (d (Syn.shift f) (Syn.shift c))
      (Syn.shift L) (Syn.shift P) (Syn.shift D) := by simpa [d,Fm.shift,Syn.shift] using hCover.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift D)) :: Γ.map Fm.shift
  have h := group_bound (Γ := Δ) (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L) (Syn.shift P)
    (Syn.shift D) (var 0) fs.wk ps.wk fam.wk cov.wk Prf.hyp0
  have size := group_length (Γ := Δ) testBody (Syn.shift P) (length (Syn.shift D))
    (data (Syn.shift m) (d (Syn.shift f) (Syn.shift c)) (Syn.shift L) (Syn.shift D)) (var 0)
  simpa [Δ,d,Syn.shift] using le_congr size (.eqRefl (Syn.shift L)) h

theorem bound (f m c L P D : PTm n) (hf : Γ ⊢[PRAAx] curveInput f m c)
    (hPoints : Γ ⊢[PRAAx] curvePoints f m P) (hFamily : Γ ⊢[PRAAx] family m (d f c) L D)
    (hCover : Γ ⊢[PRAAx] covered m (d f c) L P D) : Γ ⊢[PRAAx] le (length P) (length D * L) :=
  Foundations.FiniteCoverAssignment.cover_count testBody P (length D) (data m (d f c) L D) L
    (generic_cover _ _ _ _ _ hCover) (group_bounds _ _ _ _ _ _ hf hPoints hFamily hCover)

theorem bound_at_most (f m c L P D M : PTm n) (hf : Γ ⊢[PRAAx] curveInput f m c)
    (hPoints : Γ ⊢[PRAAx] curvePoints f m P) (hFamily : Γ ⊢[PRAAx] family m (d f c) L D)
    (hCover : Γ ⊢[PRAAx] covered m (d f c) L P D) (hM : Γ ⊢[PRAAx] le (length D) M) : Γ ⊢[PRAAx] le (length P) (M * L) :=
  le_trans (bound _ _ _ _ _ _ hf hPoints hFamily hCover) (mul_le_mul_right L hM)

def partition (m e L P D : PTm n) : PTm n := Foundations.FiniteCoverAssignment.run testBody P (length D) (data m e L D)

theorem partition_group (m e L P D g : PTm n) (hg : Γ ⊢[PRAAx] lt g (length D)) : Γ ⊢[PRAAx]
    entry (fstT (partition m e L P D)) g ≐ group m e L P D g :=
  (entry_congr (Foundations.FiniteCoverAssignment.returned_groups testBody P (length D) (data m e L D)) (.eqRefl g)).eqTrans
    (Foundations.FiniteCoverAssignment.groups_lookup testBody P (length D) (data m e L D) g hg)

theorem partition_total (m e L P D : PTm n) (h : Γ ⊢[PRAAx] covered m e L P D) : Γ ⊢[PRAAx]
    sndT (sndT (partition m e L P D)) ≐ length P :=
  Foundations.FiniteCoverAssignment.returned_partition testBody P (length D) (data m e L D) (generic_cover _ _ _ _ _ h)

theorem actual_rational_cover_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (curveInput (var 0) (var 1) (var 2) ⟶ curvePoints (var 0) (var 1) (var 4) ⟶
      family (var 1) (d (var 0) (var 2)) (var 3) (var 5) ⟶
      covered (var 1) (d (var 0) (var 2)) (var 3) (var 4) (var 5) ⟶
      le (length (var 5)) (var 6) ⟶ le (length (var 4)) (var 6 * var 3)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI
    (bound_at_most _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

theorem actual_rational_cover_partition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (covered (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      sndT (sndT (partition (var 0) (var 1) (var 2) (var 3) (var 4))) ≐ length (var 3)) :=
  closeUniv 5 (.impI (partition_total _ _ _ _ _ Prf.hyp0))

theorem actual_rational_cover_first_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (covered (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ lt (var 5) (length (var 3)) ⟶
      lt (first (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (length (var 4)) ⋏
        hasCoefficients (entry (var 4) (first (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))
          (length (entry (var 4) (first (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))))
          (count (var 0) (var 1) (var 2)) (vector (var 0) (var 1) (var 2) (abscissa (var 3) (var 5)) (ordinate (var 3) (var 5)))) :=
  closeUniv 6 (.impI (.impI (first_correct _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_rational_cover_least_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (hasCoefficients (entry (var 4) (var 6)) (length (entry (var 4) (var 6))) (count (var 0) (var 1) (var 2))
      (vector (var 0) (var 1) (var 2) (abscissa (var 3) (var 5)) (ordinate (var 3) (var 5))) ⟶
        le (first (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 6)) :=
  closeUniv 7 (.impI (first_least _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_rational_cover_group_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 5) (length (var 4)) ⟶
      entry (fstT (partition (var 0) (var 1) (var 2) (var 3) (var 4))) (var 5) ≐
        group (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (partition_group _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalSuperellipticCover
