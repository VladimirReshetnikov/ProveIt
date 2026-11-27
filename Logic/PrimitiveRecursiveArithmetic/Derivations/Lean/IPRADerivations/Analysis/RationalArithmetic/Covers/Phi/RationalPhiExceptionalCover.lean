import IPRADerivations.Analysis.RationalArithmetic.Covers.Phi.RationalPhiCoverPrefix

/-!
# Explicit rational exceptions in the original Phi_s cover bound

A genuine first-match scan assigns each original point to a matching listed
exception or to one final remainder group. Point comparison uses rational
field values, so different raw encodings of the same point match. The actual
partition and original distinctness bound the exception contribution by the
length of the supplied exception list. No exceptional points are located.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPhiExceptionalCover

open_ipra
open RationalPhiSectionNonzero (curveInput)
open RationalPhiCoverAssignment (sourceCoverBit)
open RationalCurvePointsGaussianEmbedding (distinct distinctFrom distinct_at)
open RationalSuperellipticNormDegree (pointPowers point_power_at)
open RationalArgmin (rationalEq rationalEq_congr)
open RationalPhiCoverPrefix (extra extra_at)
open GaussianRationalFiberGrouping (abscissa ordinate)
open LeanProofs.IPRA.Foundations.BoundedSyntax (BFm formula)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)


variable {n : ℕ} {Γ : List (Fm PTm n)}

def pointEqual (v w : PTm n) : Fm PTm n := rationalEq (fstT v) (fstT w) ⋏ rationalEq (sndT v) (sndT w)
def pointCode (v : PTm n) : PTm n := pairT (RationalArithmetic.recode (fstT v)) (RationalArithmetic.recode (sndT v))
def pointBit (v w : PTm n) : PTm n := eqb (pointCode v) (pointCode w)
def test (g v X : PTm n) : PTm n := RationalArithmetic.select (Signum.sg (monus (length X) g)) one (pointBit v (entry X g))
def testBody : PTm 3 := test (var 0) (var 1) (var 2)
def group (X P g : PTm n) : PTm n := Foundations.FiniteCoverAssignment.group testBody P (succ (length X)) X g
def size (X P g : PTm n) : PTm n := Foundations.FiniteCoverAssignment.groupSize testBody P (succ (length X)) X g
def remainder (X P : PTm n) : PTm n := group X P (length X)
def total (X P : PTm n) : PTm n := Foundations.FiniteCoverAssignment.total testBody P (succ (length X)) X

def outside (X P : PTm n) : Fm PTm n := .all (lt (var 0) (length (Syn.shift P)) ⟶
  .all (lt (var 0) (length (Syn.shift (Syn.shift X))) ⟶
    neg (pointEqual (entry (Syn.shift (Syn.shift P)) (var 1)) (entry (Syn.shift (Syn.shift X)) (var 0)))))

ipra_subst pointEqual
ipra_subst pointCode
ipra_subst pointBit
ipra_subst test [Signum.sg, one]
ipra_subst group
ipra_subst size
ipra_subst remainder
ipra_subst total
ipra_subst outside [Syn.subst_shift, Syn.shift_subst]

theorem point_equal_congr {v v' w w' : PTm n} (hv : Γ ⊢[PRAAx] v ≐ v') (hw : Γ ⊢[PRAAx] w ≐ w')
    (h : Γ ⊢[PRAAx] pointEqual v w) : Γ ⊢[PRAAx] pointEqual v' w' :=
  .andI (rationalEq_congr (congrFst hv) (congrFst hw) (.andE₁ h))
    (rationalEq_congr (congrSnd hv) (congrSnd hw) (.andE₂ h))
theorem point_code_equal (v w : PTm n) (h : Γ ⊢[PRAAx] pointEqual v w) : Γ ⊢[PRAAx] pointCode v ≐ pointCode w :=
  congrPairT (RationalGaussianEmbedding.scalar_recode_equal _ _ (.andE₁ h))
    (RationalGaussianEmbedding.scalar_recode_equal _ _ (.andE₂ h))
theorem point_equal_of_code (v w : PTm n) (h : Γ ⊢[PRAAx] pointCode v ≐ pointCode w) : Γ ⊢[PRAAx] pointEqual v w :=
  .andI (RationalGaussianEmbedding.rational_equal_of_scalar_recode _ _
    ((fst_pair _ _).eqSymm.eqTrans h.fstE))
    (RationalGaussianEmbedding.rational_equal_of_scalar_recode _ _
    ((snd_pair _ _).eqSymm.eqTrans h.sndE))
theorem point_equal_refl (v : PTm n) : Γ ⊢[PRAAx] pointEqual v v := point_equal_of_code v v (.eqRefl _)
theorem point_equal_symm (v w : PTm n) (h : Γ ⊢[PRAAx] pointEqual v w) : Γ ⊢[PRAAx] pointEqual w v :=
  point_equal_of_code _ _ (point_code_equal _ _ h).eqSymm
theorem point_equal_trans (v w z : PTm n) (h : Γ ⊢[PRAAx] pointEqual v w) (h' : Γ ⊢[PRAAx] pointEqual w z) :
    Γ ⊢[PRAAx] pointEqual v z := point_equal_of_code _ _ ((point_code_equal _ _ h).eqTrans (point_code_equal _ _ h'))
theorem point_bit_complete (v w : PTm n) (h : Γ ⊢[PRAAx] pointEqual v w) : Γ ⊢[PRAAx] pointBit v w ≐ one :=
  eqb_of_eq (point_code_equal _ _ h)
theorem point_bit_sound (v w : PTm n) (h : Γ ⊢[PRAAx] neg (pointBit v w ≐ zero)) : Γ ⊢[PRAAx] pointEqual v w :=
  point_equal_of_code _ _ (Foundations.FiniteFiberGrouping.equality_of_nonzero_eqb h)
theorem point_bit_cases (v w : PTm n) : Γ ⊢[PRAAx] pointBit v w ≐ zero ⋎ pointBit v w ≐ one :=
  Foundations.BoundedReflection.eqb_cases _ _

theorem test_body_at (g v X : PTm n) : inst3 testBody g v X = test g v X := by simp [testBody,inst3]
theorem test_exception (g v X : PTm n) (hg : Γ ⊢[PRAAx] lt g (length X)) : Γ ⊢[PRAAx] test g v X ≐ pointBit v (entry X g) :=
  RationalArithmetic.select_one _ _ _ (AnalyticNumberTheory.Totatives.sg_lt hg)
theorem test_default (v X : PTm n) : Γ ⊢[PRAAx] test (length X) v X ≐ one :=
  RationalArithmetic.select_zero _ _ _ (AnalyticNumberTheory.Totatives.sg_le (le_refl _))

theorem generic_cover (X P : PTm n) : Γ ⊢[PRAAx] Foundations.FiniteCoverAssignment.cover testBody P (succ (length X)) X := by
  refine .allI (.impI ?_)
  let X' := Syn.shift X
  let P' := Syn.shift P
  let Δ := lt (var 0) (length P') :: Γ.map Fm.shift
  have cover : Δ ⊢[PRAAx] Foundations.FiniteCoverAssignment.hasCover testBody (succ (length X')) (entry P' (var 0)) X' := by
    refine .exI (length X') ?_
    have hit : Δ ⊢[PRAAx] lt (length X') (succ (length X')) ⋏ neg (test (length X') (entry P' (var 0)) X' ≐ zero) :=
      .andI (le_refl _) (.impI (succ_ne_zero ((test_default (entry P' (var 0)) X').wk.eqSymm.eqTrans Prf.hyp0)))
    simpa only [Foundations.FiniteCoverAssignment.hasCover,Fm.subst_and,subst_lt,subst_neg,Fm.subst_eq,subst_inst3,Syn.subst_inst_shift,
      Syn.subst_var,Syn.inst_zero,test_body_at,subst_test,ConciseIPRA.PTm.subst_zero] using hit
  simpa only [Δ,X',P',Syn.shift,Foundations.SequenceComposition.subst_length,ConciseIPRA.PTm.subst_succ] using cover

theorem group_length (X P g : PTm n) : Γ ⊢[PRAAx] length (group X P g) ≐ size X P g := Foundations.FiniteCoverAssignment.group_length _ _ _ _ _
theorem cardinal_partition (X P : PTm n) : Γ ⊢[PRAAx] total X P ≐ length P := Foundations.FiniteCoverAssignment.cardinal_partition _ _ _ _ (generic_cover X P)
theorem group_lookup (X P g i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length (group X P g))) : Γ ⊢[PRAAx]
    entry (group X P g) i ≐ entry P (entry (Foundations.FiniteCoverAssignment.indices testBody P (succ (length X)) X g) i) :=
  Foundations.FiniteCoverAssignment.group_lookup _ _ _ _ _ _ (lt_congr (.eqRefl _) (group_length _ _ _) hi)
theorem group_index_bound (X P g i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length (group X P g))) : Γ ⊢[PRAAx]
    lt (entry (Foundations.FiniteCoverAssignment.indices testBody P (succ (length X)) X g) i) (length P) :=
  Foundations.FiniteCoverAssignment.index_bound _ _ _ _ _ _ (lt_congr (.eqRefl _) (group_length _ _ _) hi)
theorem exception_equal (X P g i : PTm n) (hg : Γ ⊢[PRAAx] lt g (length X)) (hi : Γ ⊢[PRAAx] lt i (length (group X P g))) :
    Γ ⊢[PRAAx] pointEqual (entry (group X P g) i) (entry X g) := by
  have hit : Γ ⊢[PRAAx] neg (test g (entry (group X P g) i) X ≐ zero) := by
    simpa only [test_body_at,group] using Foundations.FiniteCoverAssignment.group_test testBody P (succ (length X)) X g i (generic_cover X P)
      (lt_congr (.eqRefl _) (group_length _ _ _) hi)
  have nz : Γ ⊢[PRAAx] neg (pointBit (entry (group X P g) i) (entry X g) ≐ zero) := by
    exact .impI (.impE hit.wk ((test_exception g (entry (group X P g) i) X hg).wk.eqTrans Prf.hyp0))
  exact point_bit_sound _ _ nz

theorem remainder_outside_at (X P i g : PTm n) (hi : Γ ⊢[PRAAx] lt i (length (remainder X P)))
    (hg : Γ ⊢[PRAAx] lt g (length X)) : Γ ⊢[PRAAx] neg (pointEqual (entry (remainder X P) i) (entry X g)) := by
  let j := entry (Foundations.FiniteCoverAssignment.indices testBody P (succ (length X)) X (length X)) i
  have label : Γ ⊢[PRAAx] Foundations.FiniteCoverAssignment.label testBody P (succ (length X)) X j ≐ length X :=
    Foundations.FiniteCoverAssignment.index_label _ _ _ _ _ _ (lt_congr (.eqRefl _) (group_length _ _ _) hi)
  have earlier : Γ ⊢[PRAAx] test g (entry P j) X ≐ zero := by
    simpa only [test_body_at] using Foundations.FiniteCoverAssignment.assigned_before testBody (succ (length X)) (entry P j) X g
      (lt_congr (.eqRefl _) label.eqSymm hg)
  refine .impI ?_
  let Δ := pointEqual (entry (remainder X P) i) (entry X g) :: Γ
  have original : Δ ⊢[PRAAx] pointEqual (entry P j) (entry X g) :=
    point_equal_congr (group_lookup X P (length X) i hi).wk (.eqRefl _) Prf.hyp0
  have one : Δ ⊢[PRAAx] test g (entry P j) X ≐ one :=
    (test_exception g (entry P j) X hg).wk.eqTrans (point_bit_complete _ _ original)
  exact succ_ne_zero (one.eqSymm.eqTrans earlier.wk)

theorem remainder_outside (X P : PTm n) : Γ ⊢[PRAAx] outside X (remainder X P) := by
  refine .allI (.impI (.allI (.impI ?_)))
  let X' := Syn.shift (Syn.shift X)
  let P' := Syn.shift (Syn.shift P)
  let Δ := lt (var 0) (length X') ::
    (lt (var 1) (length (remainder X' P'))) :: (Γ.map Fm.shift).map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 1) (length (remainder X' P')) := Prf.hyp1
  have hg : Δ ⊢[PRAAx] lt (var 0) (length X') := Prf.hyp0
  simpa [Δ,X',P',Syn.shift,Fm.shift] using remainder_outside_at X' P' (var 1) (var 0) hi hg

private theorem group_distinct_at (X P g i j : PTm n) (h : Γ ⊢[PRAAx] distinct P)
    (hi : Γ ⊢[PRAAx] lt i (length (group X P g))) (hj : Γ ⊢[PRAAx] lt j (length (group X P g)))
    (hij : Γ ⊢[PRAAx] lt i j) : Γ ⊢[PRAAx] neg (pointEqual (entry (group X P g) j) (entry (group X P g) i)) := by
  let I := Foundations.FiniteCoverAssignment.indices testBody P (succ (length X)) X g
  have bi := lt_congr (.eqRefl i) (group_length X P g) hi
  have bj := lt_congr (.eqRefl j) (group_length X P g) hj
  have original : Γ ⊢[PRAAx] neg (pointEqual (entry P (entry I j)) (entry P (entry I i))) :=
    distinct_at P (entry I i) (entry I j) h (group_index_bound X P g i hi) (group_index_bound X P g j hj)
      (Foundations.FiniteCoverAssignment.indices_increasing testBody P (succ (length X)) X g i j hij bj)
  exact .impI (.impE original.wk
    (point_equal_congr (group_lookup X P g j hj).wk (group_lookup X P g i hi).wk Prf.hyp0))

theorem group_distinct (X P g : PTm n) (h : Γ ⊢[PRAAx] distinct P) : Γ ⊢[PRAAx] distinct (group X P g) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] distinct (Syn.shift P) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let G := group (Syn.shift X) (Syn.shift P) (Syn.shift g)
  let Δ := lt (var 0) (length G) :: Γ.map Fm.shift
  have hg : Δ ⊢[PRAAx] lt (var 0) (length G) := Prf.hyp0
  have inner : Δ ⊢[PRAAx] distinctFrom G (var 0) := by
    refine .allI (.impI (.impI ?_))
    let i := Syn.shift (var 0 : PTm (n+1))
    let G' := group (Syn.shift (Syn.shift X)) (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift g))
    have hi : Δ.map Fm.shift ⊢[PRAAx] lt i (length G') := by
      simpa only [i,G,G',Fm.shift,subst_lt,Foundations.SequenceComposition.subst_length,subst_group,Syn.shift] using hg.shift
    have hd : Δ.map Fm.shift ⊢[PRAAx] distinct (Syn.shift (Syn.shift P)) := by
      simpa only [Fm.shift,RationalCurvePointsGaussianEmbedding.subst_distinct,Syn.shift] using
        (hs.wk : Δ ⊢[PRAAx] distinct (Syn.shift P)).shift
    simpa only [i,G,G',pointEqual,abscissa,ordinate,Syn.shift,subst_group,GaussianRationalFiberGrouping.subst_abscissa,
      GaussianRationalFiberGrouping.subst_ordinate,subst_fstT,subst_sndT,Foundations.MasterCertificate.subst_entry] using
      group_distinct_at (Syn.shift (Syn.shift X)) (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift g)) i (var 0)
        hd.wk.wk hi.wk.wk Prf.hyp1 Prf.hyp0
  simpa only [Δ,G,Syn.shift,subst_group,Foundations.SequenceComposition.subst_length] using inner

private theorem group_power_at (f r X P g i : PTm n) (h : Γ ⊢[PRAAx] pointPowers f r P)
    (hi : Γ ⊢[PRAAx] lt i (length (group X P g))) : Γ ⊢[PRAAx]
    rationalEq (RationalScalarPowerGaussianEmbedding.power (ordinate (group X P g) i) r)
      (RationalPolynomialGaussianEmbedding.evaluate f (abscissa (group X P g) i)) := by
  have eq := group_lookup X P g i hi
  have old := point_power_at f r P _ h (group_index_bound X P g i hi)
  exact rationalEq_congr (congrAp2 RationalScalarPowerGaussianEmbedding.powerF (.eqRefl r) (congrSnd eq)).eqSymm
    (congrAp3 RationalPolynomialGaussianEmbedding.hornerF (.eqRefl (length f)) (.eqRefl f) (congrFst eq)).eqSymm old

theorem group_powers (f r X P g : PTm n) (h : Γ ⊢[PRAAx] pointPowers f r P) : Γ ⊢[PRAAx] pointPowers f r (group X P g) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointPowers (Syn.shift f) (Syn.shift r) (Syn.shift P) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_group,RationalScalarPowerGaussianEmbedding.subst_power,RationalPolynomialGaussianEmbedding.subst_evaluate,
    GaussianRationalFiberGrouping.subst_abscissa,GaussianRationalFiberGrouping.subst_ordinate] using
    group_power_at (Syn.shift f) (Syn.shift r) (Syn.shift X) (Syn.shift P) (Syn.shift g) (var 0) hs.wk Prf.hyp0

theorem group_extra (A : BFm 2) (X P g x : PTm n) (h : Γ ⊢[PRAAx] extra A P x) : Γ ⊢[PRAAx] extra A (group X P g) x := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] extra A (Syn.shift P) (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (group (Syn.shift X) (Syn.shift P) (Syn.shift g))) :: Γ.map Fm.shift
  simpa only [Syn.shift,subst_group,group,Foundations.FiniteCoverAssignment.subst_group,
    Foundations.SequenceComposition.subst_length,ConciseIPRA.PTm.subst_succ] using Foundations.FiniteCoverAssignment.group_property_at (formula A) testBody
    (Syn.shift P) (succ (length (Syn.shift X))) (Syn.shift X) (Syn.shift g) (var 0) (Syn.shift x)
    (hs.wk : Δ ⊢[PRAAx] _) (lt_congr (.eqRefl _) (group_length _ _ _) Prf.hyp0)

theorem remainder_distinct (X P : PTm n) (h : Γ ⊢[PRAAx] distinct P) : Γ ⊢[PRAAx] distinct (remainder X P) := group_distinct _ _ _ h
theorem remainder_powers (f r X P : PTm n) (h : Γ ⊢[PRAAx] pointPowers f r P) : Γ ⊢[PRAAx] pointPowers f r (remainder X P) := group_powers _ _ _ _ _ h
theorem remainder_extra (A : BFm 2) (X P x : PTm n) (h : Γ ⊢[PRAAx] extra A P x) : Γ ⊢[PRAAx] extra A (remainder X P) x := group_extra A _ _ _ _ h

theorem exception_group_bound (X P g : PTm n) (hd : Γ ⊢[PRAAx] distinct P) (hg : Γ ⊢[PRAAx] lt g (length X)) :
    Γ ⊢[PRAAx] le (length (group X P g)) one := by
  refine .orE (lt_or_le one (length (group X P g))) ?_ Prf.hyp0
  let Δ := lt one (length (group X P g)) :: Γ
  have h1 : Δ ⊢[PRAAx] lt one (length (group X P g)) := Prf.hyp0
  have h0 : Δ ⊢[PRAAx] lt zero (length (group X P g)) := le_trans (zero_lt_succ zero) (le_trans (le_succ_self one) h1)
  have e1 : Δ ⊢[PRAAx] pointEqual (entry (group X P g) one) (entry X g) := exception_equal _ _ _ _ hg.wk h1
  have e0 : Δ ⊢[PRAAx] pointEqual (entry (group X P g) zero) (entry X g) := exception_equal _ _ _ _ hg.wk h0
  exact .botE _ (.impE (group_distinct_at X P g zero one hd.wk h0 h1 (zero_lt_succ zero))
    (point_equal_trans _ _ _ e1 (point_equal_symm _ _ e0)))

/-- The actual sum over the exception labels. -/
def exceptionalTotal (X P : PTm n) : PTm n := ap2 (sumF (Foundations.FiniteCoverAssignment.sizeBody testBody))
  (length X) (Foundations.FiniteCoverAssignment.data P (succ (length X)) X)

theorem exceptional_total_bound (X P : PTm n) (hd : Γ ⊢[PRAAx] distinct P) : Γ ⊢[PRAAx] le (exceptionalTotal X P) (length X) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] distinct (Syn.shift P) := by simpa [Fm.shift,Syn.shift] using hd.shift
  have pointwise : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (length X)) ⟶
      le (inst2 (Foundations.FiniteCoverAssignment.sizeBody testBody) (var 0)
        (Syn.shift (Foundations.FiniteCoverAssignment.data P (succ (length X)) X))) (inst2 (one : PTm 2) (var 0) (Syn.shift (zero : PTm n)))) := by
    refine .allI (.impI ?_)
    let X' := Syn.shift X
    let P' := Syn.shift P
    let Δ := lt (var 0) (length X') :: Γ.map Fm.shift
    have hg : Δ ⊢[PRAAx] lt (var 0) (length X') := Prf.hyp0
    have bound := exception_group_bound X' P' (var 0) hs.wk hg
    have decode := Foundations.FiniteCoverAssignment.size_at (Γ := Δ) testBody P' (succ (length X')) X' (var 0)
    simpa [Δ,X',P',Syn.shift,inst2,one] using le_congr decode.eqSymm (.eqRefl _) (le_congr (group_length _ _ _) (.eqRefl _) bound)
  exact le_congr (.eqRefl _) (Foundations.FiniteFiberGrouping.sum_units (length X) zero)
    (sum_le_params _ _ _ _ _ pointwise)

theorem total_split (X P : PTm n) : Γ ⊢[PRAAx] total X P ≐ exceptionalTotal X P + length (remainder X P) := by
  let b := Foundations.FiniteCoverAssignment.sizeBody testBody
  let d := Foundations.FiniteCoverAssignment.data P (succ (length X)) X
  have split := sum_succ' (Γ := Γ) b (length X) d
  exact split.eqTrans (congrAdd (.eqRefl _) ((Foundations.FiniteCoverAssignment.size_at testBody P (succ (length X)) X (length X)).eqTrans
    (group_length X P (length X)).eqSymm))

theorem split_bound (X P : PTm n) (hd : Γ ⊢[PRAAx] distinct P) : Γ ⊢[PRAAx]
    le (length P) (length X + length (remainder X P)) :=
  le_congr ((total_split X P).eqSymm.eqTrans (cardinal_partition X P)) (.eqRefl _)
    (add_le_add₂ (exceptional_total_bound X P hd) (le_refl _))

/-- The source covering hypothesis is restricted to actual tuples outside X. -/
def outsideCover (A : BFm 2) (f s r X M x : PTm n) : Fm PTm n := .all
  (distinct (var 0) ⟶ pointPowers (Syn.shift f) (Syn.shift r) (var 0) ⟶ extra A (var 0) (Syn.shift x) ⟶
    outside (Syn.shift X) (var 0) ⟶ sourceCoverBit (Syn.shift s) (var 0) (Syn.shift M) ≐ one)
ipra_subst outsideCover [Syn.subst_shift, Syn.shift_subst]

theorem outside_cover_at (A : BFm 2) (f s r X M x Q : PTm n) (h : Γ ⊢[PRAAx] outsideCover A f s r X M x)
    (hd : Γ ⊢[PRAAx] distinct Q) (hp : Γ ⊢[PRAAx] pointPowers f r Q) (he : Γ ⊢[PRAAx] extra A Q x)
    (ho : Γ ⊢[PRAAx] outside X Q) : Γ ⊢[PRAAx] sourceCoverBit s Q M ≐ one := by
  have rule : Γ ⊢[PRAAx] distinct Q ⟶ pointPowers f r Q ⟶ extra A Q x ⟶ outside X Q ⟶ sourceCoverBit s Q M ≐ one := by
    simpa [outsideCover] using h.allE Q
  exact .impE (.impE (.impE (.impE rule hd) hp) he) ho

/-- A concrete cover assertion on the produced remainder suffices. -/
theorem exceptional_cover_bit_bound (f s r m X P E M : PTm n) (h : Γ ⊢[PRAAx] curveInput f s r m)
    (hd : Γ ⊢[PRAAx] distinct P) (hp : Γ ⊢[PRAAx] pointPowers f r P) (hx : Γ ⊢[PRAAx] le (length X) E)
    (hc : Γ ⊢[PRAAx] sourceCoverBit s (remainder X P) M ≐ one) : Γ ⊢[PRAAx] le (length P) (E+m*M) :=
  le_trans (split_bound X P hd) (add_le_add₂ hx (RationalPhiCoverBound.cover_bit_bound f s r m (remainder X P) M h
    (remainder_distinct X P hd) (remainder_powers f r X P hp) hc))

/-- The E+mM source corollary, with no supplied property of the remainder. -/
theorem source_bound (A : BFm 2) (f s r m X P E M x : PTm n) (h : Γ ⊢[PRAAx] curveInput f s r m)
    (hd : Γ ⊢[PRAAx] distinct P) (hp : Γ ⊢[PRAAx] pointPowers f r P) (he : Γ ⊢[PRAAx] extra A P x)
    (hx : Γ ⊢[PRAAx] le (length X) E) (hc : Γ ⊢[PRAAx] outsideCover A f s r X M x) :
    Γ ⊢[PRAAx] le (length P) (E+m*M) :=
  exceptional_cover_bit_bound f s r m X P E M h hd hp hx
    (outside_cover_at A f s r X M x (remainder X P) hc (remainder_distinct X P hd) (remainder_powers f r X P hp)
      (remainder_extra A X P x he) (remainder_outside X P))

def groups (X P : PTm n) : PTm n := Foundations.FiniteCoverAssignment.groups testBody P (succ (length X)) X
def output (X P : PTm n) : PTm n := pairT (groups X P) (pairT (remainder X P) (pairT (total X P) (pairT X P)))
def pointBitF : PR 2 := PTm.toPR (pointBit (var 0) (var 1))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (X P : PTm n) : PTm n := app outputF ![X,P]
ipra_subst exceptionalTotal
ipra_subst groups
ipra_subst output
ipra_subst run

theorem point_bit_program_at (v w : PTm n) : Γ ⊢[PRAAx] app pointBitF ![v,w] ≐ pointBit v w := by
  simpa [pointBitF] using toPR_eq (Γ := Γ) (pointBit (var 0) (var 1) : PTm 2) ![v,w]
theorem program_at (X P : PTm n) : Γ ⊢[PRAAx] run X P ≐ output X P := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![X,P]
theorem returned_groups (X P : PTm n) : Γ ⊢[PRAAx] fstT (run X P) ≐ groups X P :=
  (program_at X P).fstE
theorem returned_remainder (X P : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run X P)) ≐ remainder X P :=
  (program_at X P).sndE.fstE
private theorem returned_tail (X P : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run X P)) ≐ pairT (total X P) (pairT X P) :=
  (program_at X P).sndE.sndE
theorem returned_total (X P : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run X P))) ≐ total X P :=
  (returned_tail X P).fstE
theorem returned_exceptions (X P : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run X P)))) ≐ X :=
  (returned_tail X P).sndE.fstE
theorem returned_original (X P : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run X P)))) ≐ P :=
  (returned_tail X P).sndE.sndE
theorem returned_partition (X P : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run X P))) ≐ length P :=
  (returned_total X P).eqTrans (cardinal_partition X P)

theorem groups_length (X P : PTm n) : Γ ⊢[PRAAx] length (groups X P) ≐ succ (length X) :=
  Foundations.FiniteCoverAssignment.groups_length _ _ _ _
theorem groups_lookup (X P g : PTm n) (hg : Γ ⊢[PRAAx] lt g (succ (length X))) : Γ ⊢[PRAAx]
    entry (groups X P) g ≐ group X P g := Foundations.FiniteCoverAssignment.groups_lookup _ _ _ _ _ hg
theorem point_bit_iff (v w : PTm n) : Γ ⊢[PRAAx] Fm.iff (pointBit v w ≐ one) (pointEqual v w) :=
  .iffI (.impI (point_bit_sound _ _ (.impI (succ_ne_zero (Prf.hyp1.eqSymm.eqTrans Prf.hyp0)))))
    (.impI (point_bit_complete _ _ Prf.hyp0))
theorem returned_count_bound (A : BFm 2) (f s r m X P E M x : PTm n) (h : Γ ⊢[PRAAx] curveInput f s r m)
    (hd : Γ ⊢[PRAAx] distinct P) (hp : Γ ⊢[PRAAx] pointPowers f r P) (he : Γ ⊢[PRAAx] extra A P x)
    (hx : Γ ⊢[PRAAx] le (length X) E) (hc : Γ ⊢[PRAAx] outsideCover A f s r X M x) :
    Γ ⊢[PRAAx] le (fstT (sndT (sndT (run X P)))) (E+m*M) :=
  le_congr (returned_partition X P).eqSymm (.eqRefl _) (source_bound A f s r m X P E M x h hd hp he hx hc)

theorem actual_field_point_bit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (pointBit (var 0) (var 1) ≐ one) (pointEqual (var 0) (var 1))) := closeUniv 2 (point_bit_iff _ _)
theorem actual_exception_match_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (length (var 0)) ⟶ lt (var 3) (length (group (var 0) (var 1) (var 2))) ⟶
      pointEqual (entry (group (var 0) (var 1) (var 2)) (var 3)) (entry (var 0) (var 2))) :=
  closeUniv 4 (.impI (.impI (exception_equal _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_remainder_outside_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (outside (var 0) (remainder (var 0) (var 1))) := closeUniv 2 (remainder_outside _ _)
theorem actual_remainder_distinct_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (distinct (var 1) ⟶ distinct (remainder (var 0) (var 1))) := closeUniv 2 (.impI (remainder_distinct _ _ Prf.hyp0))
theorem actual_remainder_curve_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (pointPowers (var 0) (var 1) (var 3) ⟶ pointPowers (var 0) (var 1) (remainder (var 2) (var 3))) :=
  closeUniv 4 (.impI (remainder_powers _ _ _ _ Prf.hyp0))
theorem actual_singleton_exception_groups_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (distinct (var 1) ⟶ lt (var 2) (length (var 0)) ⟶ le (length (group (var 0) (var 1) (var 2))) one) :=
  closeUniv 3 (.impI (.impI (exception_group_bound _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_exception_partition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (total (var 0) (var 1) ≐ length (var 1)) := closeUniv 2 (cardinal_partition _ _)
theorem actual_exception_remainder_count_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (distinct (var 1) ⟶ le (length (var 1)) (length (var 0)+length (remainder (var 0) (var 1)))) :=
  closeUniv 2 (.impI (split_bound _ _ Prf.hyp0))
theorem actual_original_exceptional_cover_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (curveInput (var 0) (var 1) (var 2) (var 3) ⟶ distinct (var 5) ⟶ pointPowers (var 0) (var 2) (var 5) ⟶
      le (length (var 4)) (var 6) ⟶ sourceCoverBit (var 1) (remainder (var 4) (var 5)) (var 7) ≐ one ⟶
        le (length (var 5)) (var 6+var 3*var 7)) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (.impI (exceptional_cover_bit_bound (var 0) (var 1) (var 2) (var 3)
    (var 4) (var 5) (var 6) (var 7) (.hyp (by simp)) (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0))))))
theorem actual_original_exceptional_source_bound_closed (A : BFm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (curveInput (var 0) (var 1) (var 2) (var 3) ⟶ distinct (var 5) ⟶ pointPowers (var 0) (var 2) (var 5) ⟶
      extra A (var 5) (var 8) ⟶ le (length (var 4)) (var 6) ⟶
        outsideCover A (var 0) (var 1) (var 2) (var 4) (var 7) (var 8) ⟶ le (length (var 5)) (var 6+var 3*var 7)) :=
  closeUniv 9 (.impI (.impI (.impI (.impI (.impI (.impI (source_bound A (var 0) (var 1) (var 2) (var 3)
    (var 4) (var 5) (var 6) (var 7) (var 8) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0)))))))
theorem actual_exception_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem actual_returned_exception_partition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (fstT (sndT (sndT (run (var 0) (var 1)))) ≐ length (var 1)) := closeUniv 2 (returned_partition _ _)

end LeanProofs.IPRA.Analysis.RationalPhiExceptionalCover
