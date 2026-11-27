import IPRADerivations.Foundations.HerbrandCapsule

/-!
# An actual bounded observation-image interface

FIBER section 3.2 and C1's observe node. The finite observation bound and
image verifier are computed from the original interface programs. Soundness
and paired relation transport are derived, not client fields. All-valid
certificate independence is transferred only from the original local source
rule, with its query guard retained. No raw observation is chosen from bare
totality, and no global quotient or unbounded interface is asserted.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Foundations.RealizerObservationExport

open_ipra exports
open LeanProofs.IPRA.Foundations.RealizerComposition
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def observationBody (X : Interface) : PTm 2 := ap3 X.observe (var 0) (fstT (var 1)) (sndT (var 1))
def observationBound (X : Interface) (q p : PTm n) : PTm n :=
  succ (finiteMaximum (observationBody X) (ap2 X.bound q p) (pairT q p))
def checkerFormula (X : Interface) : BoundedSyntax.BFm 3 :=
  .ex (ap2 X.bound (var 1) (var 2))
    (.and (.eq (ap3 X.verify (var 0) (var 2) (var 3)) one)
      (.eq (var 1) (ap3 X.observe (var 0) (var 2) (var 3))))
def rawImage (X : Interface) (v q p : PTm n) : Fm PTm n :=
  .ex (lt (var 0) (ap2 X.bound (Syn.shift q) (Syn.shift p)) ⋏
    ((ap3 X.verify (var 0) (Syn.shift q) (Syn.shift p) ≐ one) ⋏
      (Syn.shift v ≐ ap3 X.observe (var 0) (Syn.shift q) (Syn.shift p))))
def image (X : Interface) (v q p : PTm n) : Fm PTm n :=
  .ex (valid X (var 0) (Syn.shift q) (Syn.shift p) ⋏
    (Syn.shift v ≐ ap3 X.observe (var 0) (Syn.shift q) (Syn.shift p)))
def output (X : Interface) : Interface where
  query := X.query
  bound := PTm.toPR (observationBound X (var 0) (var 1))
  verify := BoundedSyntax.bitF (checkerFormula X)
  observe := PTm.toPR (var 0 : PTm 3)
  related := X.related

ipra_subst observationBound
@[simp] theorem subst_image {m : ℕ} (σ : Fin n → PTm m) (X : Interface) (v q p : PTm n) :
    (image X v q p).subst σ = image X (Syn.subst σ v) (Syn.subst σ q) (Syn.subst σ p) := by
  simp only [image,Fm.subst_ex,Fm.subst_and,Fm.subst_eq,subst_valid,subst_ap3,Syn.subst_var,Syn.up_zero,
    Syn.subst_shift,Syn.shift_subst,Syn.up_succ]
@[simp] theorem subst_rawImage {m : ℕ} (σ : Fin n → PTm m) (X : Interface) (v q p : PTm n) :
    (rawImage X v q p).subst σ = rawImage X (Syn.subst σ v) (Syn.subst σ q) (Syn.subst σ p) := by
  simp only [rawImage,Fm.subst_ex,Fm.subst_and,Fm.subst_eq,subst_lt,subst_ap2,subst_ap3,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.up_zero,
    Syn.subst_shift,Syn.shift_subst,Syn.up_succ]
@[simp] theorem subst_outputTotal {m : ℕ} (σ : Fin n → PTm m) (X : Interface) (q p : PTm n) :
    (outputTotal X q p).subst σ = outputTotal X (Syn.subst σ q) (Syn.subst σ p) := by
  simp only [outputTotal,Fm.subst_ex,subst_valid,Syn.subst_var,Syn.up_zero,
    BoundedFormulas.subst_up_shift']
theorem observation_body_at (X : Interface) (c q p : PTm n) : Γ ⊢[PRAAx]
    inst2 (observationBody X) c (pairT q p) ≐ ap3 X.observe c q p := by
  simpa [observationBody,inst2] using congrAp3 X.observe (.eqRefl c) (fst_pair q p) (snd_pair q p)
theorem observation_bound (X : Interface) (c q p : PTm n)
    (hc : Γ ⊢[PRAAx] lt c (ap2 X.bound q p)) : Γ ⊢[PRAAx]
    lt (ap3 X.observe c q p) (observationBound X q p) :=
  lt_congr (observation_body_at X c q p) (.eqRefl _)
    ((succ_monus_succ _ _).eqTrans (finiteMaximum_at (observationBody X) hc))
theorem output_bound_at (X : Interface) (q p : PTm n) : Γ ⊢[PRAAx]
    ap2 (output X).bound q p ≐ observationBound X q p := by
  simpa [output,ap2] using toPR_eq (Γ := Γ) (observationBound X (var 0) (var 1)) ![q,p]
theorem output_observation_at (X : Interface) (v q p : PTm n) : Γ ⊢[PRAAx]
    ap3 (output X).observe v q p ≐ v := by
  simpa [output,ap3] using toPR_eq (Γ := Γ) (var 0 : PTm 3) ![v,q,p]
theorem output_query_at (X : Interface) (q p : PTm n) : Γ ⊢[PRAAx]
    ap2 (output X).query q p ≐ ap2 X.query q p := .eqRefl _
theorem checker_meaning (X : Interface) (v q p : PTm n) :
    (BoundedSyntax.formula (checkerFormula X)).subst ![v,q,p] = rawImage X v q p := by
  simp [checkerFormula,BoundedSyntax.formula,rawImage,Syn.up,Syn.shift]
theorem verifier_reflection (X : Interface) (v q p : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (ap3 (output X).verify v q p ≐ one) (rawImage X v q p) := by
  have e := BoundedSyntax.program_correct (checkerFormula X) ![v,q,p] (Γ := Γ)
  exact (RealizerMasterInterface.eq_one_iff e).iffTrans (by
    simpa only [checker_meaning] using BoundedSyntax.bounded_reflection (Γ := Γ) (checkerFormula X) ![v,q,p])
theorem raw_image_to_image (X : Interface) (v q p : PTm n) (h : Γ ⊢[PRAAx] rawImage X v q p) :
    Γ ⊢[PRAAx] image X v q p := by
  refine .exE h ?_
  let Δ := (lt (var 0) (ap2 X.bound (Syn.shift q) (Syn.shift p)) ⋏
    ((ap3 X.verify (var 0) (Syn.shift q) (Syn.shift p) ≐ one) ⋏
      (Syn.shift v ≐ ap3 X.observe (var 0) (Syn.shift q) (Syn.shift p)))) :: Γ.map Fm.shift
  have out : Δ ⊢[PRAAx] image X (Syn.shift v) (Syn.shift q) (Syn.shift p) := by
    apply Prf.exI (var 0)
    simpa only [Δ,image,valid,Fm.subst_and,Fm.subst_eq,subst_valid,subst_lt,subst_ap2,subst_ap3,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.andI (Prf.andI (Prf.andE₁ Prf.hyp0) (Prf.andE₁ (Prf.andE₂ (Prf.hyp0 : Δ ⊢[PRAAx] _))))
        (Prf.andE₂ (Prf.andE₂ (Prf.hyp0 : Δ ⊢[PRAAx] _)))
  simpa only [Δ,Fm.shift,subst_image,Syn.shift] using out
theorem image_intro (X : Interface) (c v q p : PTm n) (hc : Γ ⊢[PRAAx] valid X c q p)
    (hv : Γ ⊢[PRAAx] v ≐ ap3 X.observe c q p) : Γ ⊢[PRAAx] image X v q p := by
  apply Prf.exI c
  simpa only [image,Fm.subst_and,Fm.subst_eq,subst_valid,subst_ap3,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.andI hc hv
theorem image_bound (X : Interface) (v q p : PTm n) (h : Γ ⊢[PRAAx] image X v q p) :
    Γ ⊢[PRAAx] lt v (observationBound X q p) := by
  refine .exE h ?_
  let Δ := (valid X (var 0) (Syn.shift q) (Syn.shift p) ⋏
    (Syn.shift v ≐ ap3 X.observe (var 0) (Syn.shift q) (Syn.shift p))) :: Γ.map Fm.shift
  have out : Δ ⊢[PRAAx] lt (Syn.shift v) (observationBound X (Syn.shift q) (Syn.shift p)) :=
    lt_congr (Prf.andE₂ Prf.hyp0).eqSymm (.eqRefl _)
      (observation_bound X (var 0) (Syn.shift q) (Syn.shift p) (.andE₁ (.andE₁ Prf.hyp0)))
  simpa only [Δ,Fm.shift,subst_lt,subst_observationBound,Syn.shift] using out
theorem image_checked (X : Interface) (v q p : PTm n) (h : Γ ⊢[PRAAx] image X v q p) :
    Γ ⊢[PRAAx] ap3 (output X).verify v q p ≐ one := by
  apply (verifier_reflection X v q p).iffMpr
  refine .exE h ?_
  let Δ := (valid X (var 0) (Syn.shift q) (Syn.shift p) ⋏
    (Syn.shift v ≐ ap3 X.observe (var 0) (Syn.shift q) (Syn.shift p))) :: Γ.map Fm.shift
  have out : Δ ⊢[PRAAx] rawImage X (Syn.shift v) (Syn.shift q) (Syn.shift p) := by
    apply Prf.exI (var 0)
    simpa only [rawImage,Fm.subst_and,Fm.subst_eq,subst_lt,subst_ap2,subst_ap3,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.andI (Prf.andE₁ (Prf.andE₁ (Prf.hyp0 : Δ ⊢[PRAAx] _)))
        (Prf.andI (Prf.andE₂ (Prf.andE₁ Prf.hyp0)) (Prf.andE₂ Prf.hyp0))
  simpa only [Δ,Fm.shift,subst_rawImage,Syn.shift] using out
theorem validity (X : Interface) (v q p : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (valid (output X) v q p) (image X v q p) :=
  .andI (.impI (raw_image_to_image X v q p ((verifier_reflection X v q p).iffMp (.andE₂ Prf.hyp0))))
    (.impI (.andI (lt_congr (.eqRefl _) (output_bound_at X q p).eqSymm (image_bound X v q p Prf.hyp0))
      (image_checked X v q p Prf.hyp0)))
theorem observation_valid (X : Interface) (c q p : PTm n) (h : Γ ⊢[PRAAx] valid X c q p) :
    Γ ⊢[PRAAx] valid (output X) (ap3 X.observe c q p) q p :=
  (validity X _ q p).iffMpr (image_intro X c _ q p h (.eqRefl _))

def demands (q : PTm n) : PTm n := sequence (var 1) one q
def demandF : PR 2 := PTm.toPR (demands (var 0) : PTm 2)
def transform (X : Interface) (C q p : PTm n) : PTm n := ap3 X.observe (entry C zero) q p
def transformF (X : Interface) : PR 3 := PTm.toPR (transform X (var 0) (var 1) (var 2))
ipra_subst demands
ipra_subst transform
theorem demand_at (q p : PTm n) : Γ ⊢[PRAAx] ap2 demandF q p ≐ demands q := by
  simpa [demandF,ap2] using toPR_eq (Γ := Γ) (demands (var 0) : PTm 2) ![q,p]
theorem demand_length (q : PTm n) : Γ ⊢[PRAAx] length (demands q) ≐ one := MasterCertificate.sequence_length _ _ _
theorem demand_lookup (q i : PTm n) (hi : Γ ⊢[PRAAx] lt i one) : Γ ⊢[PRAAx] entry (demands q) i ≐ q :=
  MasterCertificate.sequence_decode (var 1) hi
theorem transform_at (X : Interface) (C q p : PTm n) : Γ ⊢[PRAAx]
    ap3 (transformF X) C q p ≐ transform X C q p := by
  simpa [transformF,ap3] using toPR_eq (Γ := Γ) (transform X (var 0) (var 1) (var 2)) ![C,q,p]
theorem input_certificate (X : Interface) (C q p : PTm n)
    (h : Γ ⊢[PRAAx] masterValid X (demands q) C p) : Γ ⊢[PRAAx] valid X (entry C zero) q p :=
  valid_congr X (.eqRefl _) (demand_lookup q zero (zero_lt_succ zero)) (.eqRefl _)
    (master_values_at X (.andE₂ (.andE₂ h))
      (lt_congr (.eqRefl _) (demand_length q).eqSymm (zero_lt_succ zero)))
theorem input_related (X : Interface) (C C' q p : PTm n)
    (h : Γ ⊢[PRAAx] masterRelated X (demands q) C C' p) : Γ ⊢[PRAAx] related X (entry C zero) (entry C' zero) q p :=
  related_congr X (.eqRefl _) (.eqRefl _) (demand_lookup q zero (zero_lt_succ zero)) (.eqRefl _)
    (master_related_at X h (lt_congr (.eqRefl _) (demand_length q).eqSymm (zero_lt_succ zero)))
theorem related_values (X : Interface) (v v' q p : PTm n)
    (h : Γ ⊢[PRAAx] ap4 X.related v v' q p ≐ one) : Γ ⊢[PRAAx] related (output X) v v' q p := by
  have e := congrApp (Γ := Γ) X.related
    (ts := ![ap3 (output X).observe v q p,ap3 (output X).observe v' q p,q,p]) (us := ![v,v',q,p])
    (fun i => by fin_cases i; exact output_observation_at X v q p; exact output_observation_at X v' q p
                 exact .eqRefl _; exact .eqRefl _)
  exact e.eqTrans h

/-- This constructor needs no all-valid coherence premise. Its stability
transports the relation of the actual corresponding input certificates. -/
def realizer (X : Interface) : Realizer X (output X) where
  demand := demandF
  transform := transformF X
  guard := zero ≐ zero
  residuals := []
  sound := by
    apply valid_congr (output X) (transform_at X (var 0) (var 1) (var 2)).eqSymm (.eqRefl _) (.eqRefl _)
    apply observation_valid
    apply input_certificate
    exact masterValid_congr X (demand_at (var 1) (var 2)) (.eqRefl _) (.eqRefl _) (.hyp (by simp))
  stable := by
    apply related_congr (output X) (transform_at X (var 0) (var 2) (var 3)).eqSymm
      (transform_at X (var 1) (var 2) (var 3)).eqSymm (.eqRefl _) (.eqRefl _)
    apply related_values
    apply input_related
    exact masterRelated_congr X (demand_at (var 2) (var 3)) (.eqRefl _) (.eqRefl _) (.eqRefl _) (.hyp (by simp))
def code (X : Interface) : RealizerGraph.Code := ⟨demandF,transformF X,zero ≐ zero,[]⟩
theorem realizer_code (X : Interface) : RealizerGraph.Code.ofRealizer (realizer X) = code X := rfl
def primitive (X : Interface) : RealizerGraph.Primitive X (output X) where
  code := code X
  sound := (realizer X).sound
  stable := (realizer X).stable
def program (X : Interface) : RealizerGraph.Program X (output X) := .primitive (primitive X)
theorem program_code (X : Interface) : (program X).code = code X := rfl

theorem empty_input_rejected (X : Interface) (v q p : PTm n)
    (hB : Γ ⊢[PRAAx] ap2 X.bound q p ≐ zero) : Γ ⊢[PRAAx] neg (valid (output X) v q p) := by
  refine .impI (.exE ((validity X v q p).iffMp Prf.hyp0) ?_)
  have shifted : Γ.map Fm.shift ⊢[PRAAx] ap2 X.bound (Syn.shift q) (Syn.shift p) ≐ zero := by
    simpa [Fm.shift,Syn.shift] using hB.shift
  exact lt_irrefl zero _ (lt_of_le_of_lt (zero_le _)
    (lt_congr (.eqRefl _) shifted.wk.wk (.andE₁ (.andE₁ Prf.hyp0))))

/-- Precisely the original source certificate-independence rule, retaining
its actual query guard. No output-interface law is supplied. -/
def CoherentOn (X : Interface) (G : Fm PTm 2) : Prop :=
  ∀ {n : ℕ} {Γ : List (Fm PTm n)} (c c' q p : PTm n),
    (Γ ⊢[PRAAx] queryAt G q p) → (Γ ⊢[PRAAx] valid X c q p) →
    (Γ ⊢[PRAAx] valid X c' q p) → (Γ ⊢[PRAAx] related X c c' q p)

theorem coherent_with_source (X : Interface) (G : Fm PTm 2) (hX : CoherentOn X G) (v c q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt G q p) (hv : Γ ⊢[PRAAx] valid (output X) v q p)
    (hc : Γ ⊢[PRAAx] valid X c q p) :
    Γ ⊢[PRAAx] related (output X) v (ap3 X.observe c q p) q p := by
  refine .exE ((validity X v q p).iffMp hv) ?_
  let Δ := (valid X (var 0) (Syn.shift q) (Syn.shift p) ⋏
    (Syn.shift v ≐ ap3 X.observe (var 0) (Syn.shift q) (Syn.shift p))) :: Γ.map Fm.shift
  have guard : Γ.map Fm.shift ⊢[PRAAx] queryAt G (Syn.shift q) (Syn.shift p) := by
    simpa [Fm.shift,Syn.shift] using hg.shift
  have original : Γ.map Fm.shift ⊢[PRAAx] valid X (Syn.shift c) (Syn.shift q) (Syn.shift p) := by
    simpa [Fm.shift,Syn.shift] using hc.shift
  have both := hX (Γ := Δ) (var 0) (Syn.shift c) (Syn.shift q) (Syn.shift p) guard.wk (.andE₁ Prf.hyp0) original.wk
  have out := related_congr (output X) (Prf.andE₂ (Prf.hyp0 : Δ ⊢[PRAAx] _)).eqSymm (.eqRefl _)
    (.eqRefl _) (.eqRefl _) (related_values X _ _ _ _ both)
  simpa only [Δ,Fm.shift,subst_related,subst_ap3,Syn.shift] using out
theorem coherent_export (X : Interface) (G : Fm PTm 2) (hX : CoherentOn X G) (v v' q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt G q p) (hv : Γ ⊢[PRAAx] valid (output X) v q p)
    (hv' : Γ ⊢[PRAAx] valid (output X) v' q p) : Γ ⊢[PRAAx] related (output X) v v' q p := by
  refine .exE ((validity X v' q p).iffMp hv') ?_
  let Δ := (valid X (var 0) (Syn.shift q) (Syn.shift p) ⋏
    (Syn.shift v' ≐ ap3 X.observe (var 0) (Syn.shift q) (Syn.shift p))) :: Γ.map Fm.shift
  have guard : Γ.map Fm.shift ⊢[PRAAx] queryAt G (Syn.shift q) (Syn.shift p) := by
    simpa [Fm.shift,Syn.shift] using hg.shift
  have value : Γ.map Fm.shift ⊢[PRAAx] valid (output X) (Syn.shift v) (Syn.shift q) (Syn.shift p) := by
    simpa [Fm.shift,Syn.shift] using hv.shift
  have mixed := coherent_with_source X G hX (Syn.shift v) (var 0) (Syn.shift q) (Syn.shift p)
    guard.wk value.wk (Prf.andE₁ (Prf.hyp0 : Δ ⊢[PRAAx] _))
  have out := related_congr (output X) (.eqRefl _) (Prf.andE₂ (Prf.hyp0 : Δ ⊢[PRAAx] _)).eqSymm
    (.eqRefl _) (.eqRefl _) mixed
  simpa only [Δ,Fm.shift,subst_related,Syn.shift] using out

theorem exported_totality (X : Interface) (q p : PTm n) (h : Γ ⊢[PRAAx] outputTotal X q p) :
    Γ ⊢[PRAAx] outputTotal (output X) q p := by
  refine .exE h ?_
  let Δ := valid X (var 0) (Syn.shift q) (Syn.shift p) :: Γ.map Fm.shift
  have out : Δ ⊢[PRAAx] outputTotal (output X) (Syn.shift q) (Syn.shift p) := by
    apply Prf.exI (ap3 X.observe (var 0) (Syn.shift q) (Syn.shift p))
    simpa only [outputTotal,subst_valid,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      observation_valid X (var 0) (Syn.shift q) (Syn.shift p) (Prf.hyp0 : Δ ⊢[PRAAx] _)
  simpa only [Δ,Fm.shift,subst_outputTotal,Syn.shift] using out

theorem coherent_of_invariant (X : Interface) (G : Fm PTm 2) (h : ObservationInvariant X) :
    CoherentOn X G := fun c c' q p _ hc hc' => h.apply c c' q p hc hc'

/-! ## A nonvacuous arithmetic instance: the unique certificate is the query -/

def sumInput : Interface where
  query := PTm.toPR (one : PTm 2)
  bound := PTm.toPR (succ (var 0) : PTm 2)
  verify := PTm.toPR (eqb (var 0) (var 1) : PTm 3)
  observe := PTm.toPR (var 0+var 2 : PTm 3)
  related := PTm.toPR (eqb (var 0) (var 1) : PTm 4)

theorem sum_query_at (q p : PTm n) : Γ ⊢[PRAAx] ap2 sumInput.query q p ≐ one := by
  simpa [sumInput,ap2] using toPR_eq (Γ := Γ) (one : PTm 2) ![q,p]
theorem sum_bound_at (q p : PTm n) : Γ ⊢[PRAAx] ap2 sumInput.bound q p ≐ succ q := by
  simpa [sumInput,ap2] using toPR_eq (Γ := Γ) (succ (var 0) : PTm 2) ![q,p]
theorem sum_verifier_at (c q p : PTm n) : Γ ⊢[PRAAx] ap3 sumInput.verify c q p ≐ eqb c q := by
  simpa [sumInput,ap3] using toPR_eq (Γ := Γ) (eqb (var 0) (var 1) : PTm 3) ![c,q,p]
theorem sum_observation_at (c q p : PTm n) : Γ ⊢[PRAAx] ap3 sumInput.observe c q p ≐ c+p := by
  simpa [sumInput,ap3] using toPR_eq (Γ := Γ) (var 0+var 2 : PTm 3) ![c,q,p]
theorem sum_relation_at (v v' q p : PTm n) : Γ ⊢[PRAAx]
    ap4 sumInput.related v v' q p ≐ eqb v v' := by
  simpa [sumInput,ap4] using toPR_eq (Γ := Γ) (eqb (var 0) (var 1) : PTm 4) ![v,v',q,p]
theorem sum_certificate (c q p : PTm n) (h : Γ ⊢[PRAAx] valid sumInput c q p) :
    Γ ⊢[PRAAx] c ≐ q :=
  BoundedReflection.eq_of_eqb ((sum_verifier_at c q p).eqSymm.eqTrans (.andE₂ h))
theorem sum_self_valid (q p : PTm n) : Γ ⊢[PRAAx] valid sumInput q q p :=
  .andI (lt_congr (.eqRefl _) (sum_bound_at q p).eqSymm (le_refl (succ q)))
    ((sum_verifier_at q q p).eqTrans (eqb_of_eq (.eqRefl _)))
theorem sum_input_validity (c q p : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (valid sumInput c q p) (c ≐ q) :=
  .andI (.impI (sum_certificate c q p Prf.hyp0))
    (.impI (valid_congr sumInput Prf.hyp0.eqSymm (.eqRefl _) (.eqRefl _) (sum_self_valid q p)))
theorem sum_totality (q p : PTm n) : Γ ⊢[PRAAx] outputTotal sumInput q p := by
  apply Prf.exI q
  simpa only [outputTotal,subst_valid,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using sum_self_valid (Γ := Γ) q p
theorem sum_coherent (G : Fm PTm 2) : CoherentOn sumInput G := by
  intro n Γ c c' q p _ hc hc'
  have e := (sum_certificate c q p hc).eqTrans (sum_certificate c' q p hc').eqSymm
  have obs := congrAp3 sumInput.observe e (.eqRefl q) (.eqRefl p)
  exact (sum_relation_at _ _ q p).eqTrans (eqb_of_eq obs)
theorem sum_export_valid (q p : PTm n) : Γ ⊢[PRAAx] valid (output sumInput) (q+p) q p :=
  valid_congr (output sumInput) (sum_observation_at q q p) (.eqRefl _) (.eqRefl _)
    (observation_valid sumInput q q p (sum_self_valid q p))
theorem sum_export_unique (v q p : PTm n) (h : Γ ⊢[PRAAx] valid (output sumInput) v q p) :
    Γ ⊢[PRAAx] v ≐ q+p := by
  refine .exE ((validity sumInput v q p).iffMp h) ?_
  let Δ := (valid sumInput (var 0) (Syn.shift q) (Syn.shift p) ⋏
    (Syn.shift v ≐ ap3 sumInput.observe (var 0) (Syn.shift q) (Syn.shift p))) :: Γ.map Fm.shift
  have c := sum_certificate (Γ := Δ) (var 0) (Syn.shift q) (Syn.shift p) (.andE₁ Prf.hyp0)
  have out : Δ ⊢[PRAAx] Syn.shift v ≐ Syn.shift q+Syn.shift p :=
    (Prf.andE₂ Prf.hyp0).eqTrans ((sum_observation_at _ _ _).eqTrans (congrAdd c (.eqRefl _)))
  simpa only [Δ,Fm.shift,Fm.subst_eq,LeanProofs.IPRA.PTm.subst_add,Syn.shift] using out
theorem sum_output_validity (v q p : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (valid (output sumInput) v q p) (v ≐ q+p) :=
  .andI (.impI (sum_export_unique v q p Prf.hyp0))
    (.impI (valid_congr (output sumInput) Prf.hyp0.eqSymm (.eqRefl _) (.eqRefl _) (sum_export_valid q p)))

/-- An actual original-input master, not a witness chosen from totality. -/
def sumMaster (q : PTm n) : PTm n := sequence (var 1) (length (demands q)) q
def sumRun (q p : PTm n) : PTm n := ap3 (transformF sumInput) (sumMaster q) q p
def sumRunF : PR 2 := PTm.toPR (sumRun (var 0) (var 1))
ipra_subst sumMaster
ipra_subst sumRun
theorem sum_master_valid (q p : PTm n) : Γ ⊢[PRAAx] masterValid sumInput (demands q) (sumMaster q) p := by
  apply canonical_master
  refine .allI (.impI ?_)
  have range : lt (var 0) (length (Syn.shift (demands q))) :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) one :=
    lt_congr (.eqRefl _) (by simpa only [subst_demands,Syn.shift] using (demand_length (Γ := Γ.map Fm.shift) (Syn.shift q)).wk) Prf.hyp0
  have point := valid_congr sumInput (.eqRefl _) (demand_lookup (Syn.shift q) (var 0) range).eqSymm
    (.eqRefl _) (sum_self_valid (Syn.shift q) (Syn.shift p))
  simpa [inst2,subst_demands,Syn.shift] using point
theorem sum_master_entry (q : PTm n) : Γ ⊢[PRAAx] entry (sumMaster q) zero ≐ q := by
  apply MasterCertificate.sequence_decode (var 1)
  exact lt_congr (.eqRefl _) (demand_length q).eqSymm (zero_lt_succ zero)
theorem sum_run (q p : PTm n) : Γ ⊢[PRAAx] sumRun q p ≐ q+p :=
  (transform_at sumInput (sumMaster q) q p).eqTrans
    ((sum_observation_at _ q p).eqTrans (congrAdd (sum_master_entry q) (.eqRefl _)))
theorem sum_program_at (q p : PTm n) : Γ ⊢[PRAAx] ap2 sumRunF q p ≐ sumRun q p := by
  simpa [sumRunF,ap2] using toPR_eq (Γ := Γ) (sumRun (var 0) (var 1)) ![q,p]
theorem sum_program (q p : PTm n) : Γ ⊢[PRAAx] ap2 sumRunF q p ≐ q+p :=
  (sum_program_at q p).eqTrans (sum_run q p)
theorem sum_program_valid (q p : PTm n) : Γ ⊢[PRAAx] valid (output sumInput) (ap2 sumRunF q p) q p :=
  (sum_output_validity _ q p).iffMpr (sum_program q p)

/-! ## Closed source contracts and literal program metadata -/

theorem observation_image_closed (X : Interface) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (Fm.iff (valid (output X) (var 0) (var 1) (var 2)) (image X (var 0) (var 1) (var 2))) :=
  closeUniv 3 (validity X _ _ _)
theorem observation_bound_closed (X : Interface) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 0) (ap2 X.bound (var 1) (var 2)) ⟶
      lt (ap3 X.observe (var 0) (var 1) (var 2)) (observationBound X (var 1) (var 2))) :=
  closeUniv 3 (.impI (observation_bound X _ _ _ Prf.hyp0))
theorem observation_demand_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((ap2 demandF (var 0) (var 1) ≐ demands (var 0)) ⋏ (length (demands (var 0)) ≐ one)) :=
  closeUniv 2 (.andI (demand_at _ _) (demand_length _))
theorem observation_transform_closed (X : Interface) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 (transformF X) (var 0) (var 1) (var 2) ≐ ap3 X.observe (entry (var 0) zero) (var 1) (var 2)) :=
  closeUniv 3 (transform_at X _ _ _)
theorem observation_empty_closed (X : Interface) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 X.bound (var 1) (var 2) ≐ zero ⟶ neg (valid (output X) (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (empty_input_rejected X _ _ _ Prf.hyp0))
theorem observation_totality_closed (X : Interface) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (outputTotal X (var 0) (var 1) ⟶ outputTotal (output X) (var 0) (var 1)) :=
  closeUniv 2 (.impI (exported_totality X _ _ Prf.hyp0))
theorem observation_coherent_closed (X : Interface) (G : Fm PTm 2) (hX : CoherentOn X G) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (queryAt G (var 2) (var 3) ⟶ valid (output X) (var 0) (var 2) (var 3) ⟶
      valid (output X) (var 1) (var 2) (var 3) ⟶ related (output X) (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (coherent_export X G hX _ _ _ _ (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))
theorem observation_sound (X : Interface) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (soundFormula (realizer X)) :=
  bounded_realizer_soundness (realizer X)
theorem observation_stable (X : Interface) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (stabilityFormula (realizer X)) :=
  bounded_realizer_stability (realizer X)
theorem observation_sealed (X : Interface) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (sealedFormula (realizer X)) :=
  bounded_realizer_sealed (realizer X)
theorem observation_programs (X : Interface) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (metadataFormula (realizer X)) :=
  realizer_program_metadata (realizer X)
theorem sum_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (Fm.iff (valid sumInput (var 0) (var 1) (var 2)) (var 0 ≐ var 1)) :=
  closeUniv 3 (sum_input_validity _ _ _)
theorem sum_total_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (outputTotal sumInput (var 0) (var 1)) :=
  closeUniv 2 (sum_totality _ _)
theorem sum_export_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (Fm.iff (valid (output sumInput) (var 0) (var 1) (var 2)) (var 0 ≐ var 1+var 2)) :=
  closeUniv 3 (sum_output_validity _ _ _)
theorem sum_master_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (masterValid sumInput (demands (var 0)) (sumMaster (var 0)) (var 1)) :=
  closeUniv 2 (sum_master_valid _ _)
theorem sum_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((ap2 sumRunF (var 0) (var 1) ≐ var 0+var 1) ⋏
      valid (output sumInput) (ap2 sumRunF (var 0) (var 1)) (var 0) (var 1)) :=
  closeUniv 2 (.andI (sum_program _ _) (sum_program_valid _ _))

end LeanProofs.IPRA.Foundations.RealizerObservationExport
