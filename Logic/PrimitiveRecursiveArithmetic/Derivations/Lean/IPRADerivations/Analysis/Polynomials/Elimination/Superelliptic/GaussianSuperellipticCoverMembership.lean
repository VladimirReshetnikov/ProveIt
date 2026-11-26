import IPRADerivations.Analysis.RationalArithmetic.Spans.Membership.GaussianRationalOriginalSpanMembership
import IPRADerivations.Foundations.FiniteCoverAssignment

/-!
# Actual membership assignment for a finite family of proper row spans

Each family entry is its original matrix, with its row count read from
that code. The fixed candidate test computes the original monomial
evaluation vector and applies the exact original-span classifier.
Original existential cover witnesses derive bounded first-assignment
coverage; actual assigned groups inherit exact original span membership.
The geometric group bound and final covering count are separate consumers.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSuperellipticCoverMembership

open_ipra
open GaussianSuperellipticSubspaceWitness (basisCount)
open GaussianSuperellipticSubspaceFromSpan (hasCoefficients pointMembership)
open GaussianRationalOriginalSpanRank (properSpan)
open GaussianRationalRowElimination (shape)
open GaussianRationalPolynomialDegree (degree)
open GaussianWeightedMonomialBasis (evaluationVector)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def matrix (D g : PTm n) : PTm n := entry D g
def rows (D g : PTm n) : PTm n := length (matrix D g)
def point (f m c L v : PTm n) : PTm n := evaluationVector m (degree f c) L (fstT v) (sndT v)
def candidate (f m c L D g v : PTm n) : PTm n :=
  GaussianRationalOriginalSpanMembership.test (matrix D g) (rows D g) (basisCount f m c L) (point f m c L v)
def data (f m c L D : PTm n) : PTm n := pairT f (pairT m (pairT c (pairT L D)))
def fields (q : PTm n) : Fin 5 → PTm n :=
  ![fstT q,fstT (sndT q),fstT (sndT (sndT q)),fstT (sndT (sndT (sndT q))),sndT (sndT (sndT (sndT q)))]
def testBody : PTm 3 := eqb (candidate (fields (var 2) 0) (fields (var 2) 1) (fields (var 2) 2)
  (fields (var 2) 3) (fields (var 2) 4) (var 0) (var 1)) one
def family (f m c L D : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift D)) ⟶
    shape (matrix (Syn.shift D) (var 0)) (rows (Syn.shift D) (var 0))
      (basisCount (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L)) ⋏
    properSpan (matrix (Syn.shift D) (var 0)) (rows (Syn.shift D) (var 0))
      (basisCount (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L)))
def coveredAt (f m c L D v : PTm n) : Fm PTm n := .ex
  (lt (var 0) (length (Syn.shift D)) ⋏
    hasCoefficients (matrix (Syn.shift D) (var 0)) (rows (Syn.shift D) (var 0))
      (basisCount (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L))
      (point (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L) (Syn.shift v)))
def covered (f m c L P D : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift P)) ⟶ coveredAt (Syn.shift f) (Syn.shift m) (Syn.shift c)
    (Syn.shift L) (Syn.shift D) (entry (Syn.shift P) (var 0)))
def group (f m c L P D g : PTm n) : PTm n :=
  Foundations.FiniteCoverAssignment.group testBody P (length D) (data f m c L D) g

ipra_subst matrix
ipra_subst rows
ipra_subst point
ipra_subst candidate
ipra_subst data
@[simp] theorem subst_fields {k : ℕ} (σ : Fin n → PTm k) (q : PTm n) (i : Fin 5) :
    Syn.subst σ (fields q i) = fields (Syn.subst σ q) i := by fin_cases i <;> simp [fields]
ipra_subst family [Syn.subst_shift, Syn.shift_subst]
ipra_subst coveredAt [Syn.subst_shift, Syn.shift_subst]
ipra_subst covered [Syn.subst_shift, Syn.shift_subst]
ipra_subst group

theorem fields_at (f m c L D : PTm n) (j : Fin 5) : Γ ⊢[PRAAx] fields (data f m c L D) j ≐ ![f,m,c,L,D] j := by
  have a := snd_pair (Γ := Γ) f (pairT m (pairT c (pairT L D)))
  have b := (congrSnd a).eqTrans (snd_pair m (pairT c (pairT L D)))
  have cc := (congrSnd b).eqTrans (snd_pair c (pairT L D))
  fin_cases j
  · exact fst_pair _ _
  · exact a.fstE
  · exact b.fstE
  · exact cc.fstE
  · exact cc.sndE

theorem point_congr {f f' m m' c c' L L' v v' : PTm n} (hf : Γ ⊢[PRAAx] f ≐ f')
    (hm : Γ ⊢[PRAAx] m ≐ m') (hc : Γ ⊢[PRAAx] c ≐ c') (hL : Γ ⊢[PRAAx] L ≐ L')
    (hv : Γ ⊢[PRAAx] v ≐ v') : Γ ⊢[PRAAx] point f m c L v ≐ point f' m' c' L' v' := by
  ipra_congr (point (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [hf, hm, hc, hL, hv]
theorem count_congr {f f' m m' c c' L L' : PTm n} (hf : Γ ⊢[PRAAx] f ≐ f')
    (hm : Γ ⊢[PRAAx] m ≐ m') (hc : Γ ⊢[PRAAx] c ≐ c') (hL : Γ ⊢[PRAAx] L ≐ L') :
    Γ ⊢[PRAAx] basisCount f m c L ≐ basisCount f' m' c' L' := by
  ipra_congr (basisCount (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hf, hm, hc, hL]
theorem classifier_congr {A A' R R' N N' v v' : PTm n} (hA : Γ ⊢[PRAAx] A ≐ A')
    (hR : Γ ⊢[PRAAx] R ≐ R') (hN : Γ ⊢[PRAAx] N ≐ N') (hv : Γ ⊢[PRAAx] v ≐ v') : Γ ⊢[PRAAx]
    GaussianRationalOriginalSpanMembership.test A R N v ≐ GaussianRationalOriginalSpanMembership.test A' R' N' v' := by
  ipra_congr (GaussianRationalOriginalSpanMembership.test (var 0) (var 1) (var 2) (var 3) : PTm 4) with
    [hA, hR, hN, hv]

theorem test_body_at (f m c L D g v : PTm n) : Γ ⊢[PRAAx]
    inst3 testBody g v (data f m c L D) ≐ eqb (candidate f m c L D g v) one := by
  have a := entry_congr (fields_at (Γ := Γ) f m c L D 4) (.eqRefl g)
  have eq := classifier_congr a (congrFst a)
    (count_congr (fields_at f m c L D 0) (fields_at f m c L D 1) (fields_at f m c L D 2) (fields_at f m c L D 3))
    (point_congr (fields_at f m c L D 0) (fields_at f m c L D 1) (fields_at f m c L D 2) (fields_at f m c L D 3) (.eqRefl v))
  simp only [testBody,inst3,subst_eqb,subst_candidate,subst_fields,Syn.subst_var,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
  exact Foundations.FiniteFiberGrouping.eqb_congr eq (.eqRefl _)

theorem family_at (f m c L D g : PTm n) (h : Γ ⊢[PRAAx] family f m c L D)
    (hg : Γ ⊢[PRAAx] lt g (length D)) : Γ ⊢[PRAAx]
    shape (matrix D g) (rows D g) (basisCount f m c L) ⋏ properSpan (matrix D g) (rows D g) (basisCount f m c L) := by
  have rule : Γ ⊢[PRAAx] lt g (length D) ⟶
      shape (matrix D g) (rows D g) (basisCount f m c L) ⋏ properSpan (matrix D g) (rows D g) (basisCount f m c L) := by
    simpa [family] using h.allE g
  exact .impE rule hg

theorem candidate_complete (f m c L D g v : PTm n)
    (hShape : Γ ⊢[PRAAx] shape (matrix D g) (rows D g) (basisCount f m c L))
    (h : Γ ⊢[PRAAx] hasCoefficients (matrix D g) (rows D g) (basisCount f m c L) (point f m c L v)) : Γ ⊢[PRAAx]
    inst3 testBody g v (data f m c L D) ≐ one :=
  (test_body_at f m c L D g v).eqTrans (eqb_of_eq
    (GaussianRationalOriginalSpanMembership.test_complete (matrix D g) (rows D g) (basisCount f m c L) (point f m c L v) hShape h))

theorem candidate_sound (f m c L D g v : PTm n)
    (h : Γ ⊢[PRAAx] neg (inst3 testBody g v (data f m c L D) ≐ zero)) : Γ ⊢[PRAAx]
    hasCoefficients (matrix D g) (rows D g) (basisCount f m c L) (point f m c L v) := by
  have bit := Foundations.FiniteFiberGrouping.equality_of_nonzero_eqb
    (.impI (.impE h.wk ((test_body_at f m c L D g v).wk.eqTrans Prf.hyp0)))
  exact GaussianRationalOriginalSpanMembership.accepted_hasCoefficients _ _ _ _ bit

theorem coveredAt_reflected (f m c L D v : PTm n) (hF : Γ ⊢[PRAAx] family f m c L D)
    (h : Γ ⊢[PRAAx] coveredAt f m c L D v) : Γ ⊢[PRAAx]
    Foundations.FiniteCoverAssignment.hasCover testBody (length D) v (data f m c L D) := by
  have Fs : Γ.map Fm.shift ⊢[PRAAx] family (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L) (Syn.shift D) := by
    simpa only [Fm.shift,subst_family,Syn.shift] using hF.shift
  refine .exE h ?_
  let Δ := (lt (var 0) (length (Syn.shift D)) ⋏
    hasCoefficients (matrix (Syn.shift D) (var 0)) (rows (Syn.shift D) (var 0))
      (basisCount (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L))
      (point (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L) (Syn.shift v))) :: Γ.map Fm.shift
  have accepted := candidate_complete (Γ := Δ) (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L) (Syn.shift D)
    (var 0) (Syn.shift v) (.andE₁ (family_at _ _ _ _ _ _ Fs.wk (.andE₁ Prf.hyp0))) (.andE₂ Prf.hyp0)
  have out : Δ ⊢[PRAAx] Foundations.FiniteCoverAssignment.hasCover testBody (length (Syn.shift D)) (Syn.shift v)
      (data (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L) (Syn.shift D)) := by
    refine .exI (var 0) ?_
    have nonzero : Δ ⊢[PRAAx] neg (inst3 testBody (var 0) (Syn.shift v)
        (data (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L) (Syn.shift D)) ≐ zero) :=
      .impI (succ_ne_zero (accepted.wk.eqSymm.eqTrans Prf.hyp0))
    simpa only [Foundations.FiniteCoverAssignment.hasCover,Fm.subst_and,subst_lt,subst_neg,Fm.subst_eq,
      subst_inst3,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,ConciseIPRA.PTm.subst_zero] using
      Prf.andI (.andE₁ (Prf.hyp0 : Δ ⊢[PRAAx] _)) nonzero
  simpa only [Δ,Fm.shift,Foundations.FiniteCoverAssignment.subst_hasCover,subst_length,subst_data,Syn.shift] using out

theorem covered_at (f m c L P D i : PTm n) (h : Γ ⊢[PRAAx] covered f m c L P D)
    (hi : Γ ⊢[PRAAx] lt i (length P)) : Γ ⊢[PRAAx] coveredAt f m c L D (entry P i) := by
  have rule : Γ ⊢[PRAAx] lt i (length P) ⟶ coveredAt f m c L D (entry P i) := by
    simpa [covered] using h.allE i
  exact .impE rule hi

theorem generic_cover (f m c L P D : PTm n) (hF : Γ ⊢[PRAAx] family f m c L D)
    (h : Γ ⊢[PRAAx] covered f m c L P D) : Γ ⊢[PRAAx]
    Foundations.FiniteCoverAssignment.cover testBody P (length D) (data f m c L D) := by
  have Fs : Γ.map Fm.shift ⊢[PRAAx] family (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L) (Syn.shift D) := by
    simpa only [Fm.shift,subst_family,Syn.shift] using hF.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] covered (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L) (Syn.shift P) (Syn.shift D) := by
    simpa only [Fm.shift,subst_covered,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift P)) :: Γ.map Fm.shift
  have reflected := coveredAt_reflected (Γ := Δ) (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L) (Syn.shift D)
    (entry (Syn.shift P) (var 0)) Fs.wk (covered_at _ _ _ _ _ _ _ cs.wk Prf.hyp0)
  simpa only [Δ,Syn.shift,subst_length,subst_data] using reflected

theorem group_hasCoefficients (f m c L P D g r : PTm n) (hF : Γ ⊢[PRAAx] family f m c L D)
    (h : Γ ⊢[PRAAx] covered f m c L P D) (hr : Γ ⊢[PRAAx] lt r (length (group f m c L P D g))) : Γ ⊢[PRAAx]
    hasCoefficients (matrix D g) (rows D g) (basisCount f m c L) (point f m c L (entry (group f m c L P D g) r)) := by
  have size : Γ ⊢[PRAAx] lt r (Foundations.FiniteCoverAssignment.groupSize testBody P (length D) (data f m c L D) g) :=
    lt_congr (.eqRefl _) (Foundations.FiniteCoverAssignment.group_length testBody P (length D) (data f m c L D) g) hr
  exact candidate_sound f m c L D g _ (Foundations.FiniteCoverAssignment.group_test testBody P (length D)
    (data f m c L D) g r (generic_cover f m c L P D hF h) size)

theorem pointMembership_groups (f m c L P D g : PTm n) (hF : Γ ⊢[PRAAx] family f m c L D)
    (h : Γ ⊢[PRAAx] covered f m c L P D) : Γ ⊢[PRAAx]
    pointMembership f m c L (group f m c L P D g) (matrix D g) (rows D g) := by
  have Fs : Γ.map Fm.shift ⊢[PRAAx] family (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L) (Syn.shift D) := by
    simpa only [Fm.shift,subst_family,Syn.shift] using hF.shift
  have cs : Γ.map Fm.shift ⊢[PRAAx] covered (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L) (Syn.shift P) (Syn.shift D) := by
    simpa only [Fm.shift,subst_covered,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (group (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L) (Syn.shift P) (Syn.shift D) (Syn.shift g))) :: Γ.map Fm.shift
  simpa only [Δ,Syn.shift,subst_group,subst_matrix,subst_rows,point,
    GaussianSuperellipticSubspaceFromSpan.pointVector,GaussianRationalFiberGrouping.abscissa,GaussianRationalFiberGrouping.ordinate] using
    group_hasCoefficients (Γ := Δ) (Syn.shift f) (Syn.shift m) (Syn.shift c) (Syn.shift L) (Syn.shift P) (Syn.shift D) (Syn.shift g)
      (var 0) Fs.wk cs.wk Prf.hyp0

def testF : PR 3 := PTm.toPR testBody
def testRun (g v p : PTm n) : PTm n := ap3 testF g v p
def groupF : PR 7 := PTm.toPR (group (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def groupRun (f m c L P D g : PTm n) : PTm n := app groupF ![f,m,c,L,P,D,g]
ipra_subst testRun
ipra_subst groupRun
theorem test_program_at (g v p : PTm n) : Γ ⊢[PRAAx] testRun g v p ≐ inst3 testBody g v p := by
  simpa [testRun,testF,inst3,ap3] using toPR_eq (Γ := Γ) testBody ![g,v,p]
theorem group_program_at (f m c L P D g : PTm n) : Γ ⊢[PRAAx] groupRun f m c L P D g ≐ group f m c L P D g := by
  simpa [groupRun,groupF] using toPR_eq (Γ := Γ)
    (group (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![f,m,c,L,P,D,g]
theorem returned_group_length (f m c L P D g : PTm n) : Γ ⊢[PRAAx]
    length (groupRun f m c L P D g) ≐ Foundations.FiniteCoverAssignment.groupSize testBody P (length D) (data f m c L D) g :=
  (congrFst (group_program_at f m c L P D g)).eqTrans
    (Foundations.FiniteCoverAssignment.group_length testBody P (length D) (data f m c L D) g)

theorem actual_family_at_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (family (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ lt (var 5) (length (var 4)) ⟶
      shape (matrix (var 4) (var 5)) (rows (var 4) (var 5)) (basisCount (var 0) (var 1) (var 2) (var 3)) ⋏
        properSpan (matrix (var 4) (var 5)) (rows (var 4) (var 5)) (basisCount (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 6 (.impI (.impI (family_at _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_candidate_sound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (neg (inst3 testBody (var 5) (var 6) (data (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ zero) ⟶
      hasCoefficients (matrix (var 4) (var 5)) (rows (var 4) (var 5)) (basisCount (var 0) (var 1) (var 2) (var 3))
        (point (var 0) (var 1) (var 2) (var 3) (var 6))) := closeUniv 7 (.impI (candidate_sound _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_candidate_complete_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (shape (matrix (var 4) (var 5)) (rows (var 4) (var 5)) (basisCount (var 0) (var 1) (var 2) (var 3)) ⟶
      hasCoefficients (matrix (var 4) (var 5)) (rows (var 4) (var 5)) (basisCount (var 0) (var 1) (var 2) (var 3))
        (point (var 0) (var 1) (var 2) (var 3) (var 6)) ⟶
          inst3 testBody (var 5) (var 6) (data (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ one) :=
  closeUniv 7 (.impI (.impI (candidate_complete _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_generic_cover_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (family (var 0) (var 1) (var 2) (var 3) (var 5) ⟶ covered (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      Foundations.FiniteCoverAssignment.cover testBody (var 4) (length (var 5)) (data (var 0) (var 1) (var 2) (var 3) (var 5))) :=
  closeUniv 6 (.impI (.impI (generic_cover _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_group_point_membership_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (family (var 0) (var 1) (var 2) (var 3) (var 5) ⟶ covered (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      pointMembership (var 0) (var 1) (var 2) (var 3) (group (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (matrix (var 5) (var 6)) (rows (var 5) (var 6))) :=
  closeUniv 7 (.impI (.impI (pointMembership_groups _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_test_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (testRun (var 0) (var 1) (var 2) ≐ inst3 testBody (var 0) (var 1) (var 2)) := closeUniv 3 (test_program_at _ _ _)
theorem actual_group_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (groupRun (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
      group (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) := closeUniv 7 (group_program_at _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianSuperellipticCoverMembership
