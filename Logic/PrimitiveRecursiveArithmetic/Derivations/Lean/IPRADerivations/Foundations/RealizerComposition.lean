import IPRADerivations.Foundations.SequenceComposition
import IPRADerivations.Foundations.BoundedFormulas
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.SubstCommand
import IPRADerivations.Core.Header

/-!
# Composition of bounded finite-query certificate realizers

The query convention is `(q,p)`: a runtime query followed by its persistent
parameter. Certificate and observation programs take `(c,q,p)`.
Demand lists, submaster extraction and intermediate masters are actual PR
programs. Numerical master bounds are obtained from canonical sequence
re-encoding using the interface's pointwise certificate caps.

`Interface` is the fixed PR-data projection of a source interface. Its
additional soundness, Boolean, quotient or metric laws can be supplied
separately; the composition proof does not synthesize those application laws.
`Realizer` uses the proved standard canonical cap-sequence master convention,
and requires the literal local soundness and relation-stability sequents.
An existing realizer with a different numerical master bound or verifier
requires a proved normalization adapter before it can inhabit this record;
no such arbitrary external adapter is silently assumed here.

The constructor retains each query guard (including precision/separation
conditions), every specialized residual family, and the exact chosen
query-indexed observation relation. This is the bounded realizer composition
kernel of FIBER `thm:composition`; concrete metric instances and translation
of arbitrary compiler graphs remain separate.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.RealizerComposition

open_ipra
open LeanProofs.IPRA.Foundations.MasterCertificate
  (sequence stack stack_zero stack_succ sequence_length sequence_decode entry)
open LeanProofs.IPRA.Foundations.SequenceComposition
  (length block prefixSum flatMap flatMap_length flatMap_lookup entry_congr)
open LeanProofs.IPRA.Foundations.BoundedReflection

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def ap4 (f : PR 4) (a b c d : PTm n) : PTm n := app f ![a, b, c, d]

@[simp] theorem subst_ap4 {m : ℕ} (σ : Fin n → PTm m) (f : PR 4) (a b c d : PTm n) :
    Syn.subst σ (ap4 f a b c d) = ap4 f (Syn.subst σ a) (Syn.subst σ b)
      (Syn.subst σ c) (Syn.subst σ d) := by
  show app _ _ = app _ _
  congr 1
  funext i
  fin_cases i <;> rfl

alias pair_congr := Common.congrPairT

/-- Monotonicity of the actual quadratic pairing code. -/
theorem pair_mono {a b A B : PTm n} (ha : Γ ⊢[PRAAx] le a A) (hb : Γ ⊢[PRAAx] le b B) :
    Γ ⊢[PRAAx] le (pairT a b) (pairT A B) := by
  have ea := natEq (eq_add_of_le ha)
  have eb := natEq (eq_add_of_le hb)
  refine le_of_eq_add (d := (monus A a + monus B b) *
      (a + b + a + b + monus A a + monus B b) + monus A a) ?_
  unfold pairT
  apply deriveNat
  ipra_simps
  rw [ea, eb]
  ring

/-- Pointwise caps bound the canonical reverse stack, with a QF induction
invariant even when the external contract contains a bounded quantifier. -/
theorem stack_mono (f g : PTm 2) (N x y : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift y)))) :
    Γ ⊢[PRAAx] le (stack f N x) (stack g N y) := by
  let P := le (stack f (var 0) (Syn.shift x)) (stack g (var 0) (Syn.shift y))
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N (le_QF _ _) ?_ ?_
    · simp only [P, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact le_congr (stack_zero f x).eqSymm (stack_zero g y).eqSymm (le_refl zero)
    · simp only [P, subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact .impI (le_congr (stack_succ _ _ _).eqSymm (stack_succ _ _ _).eqSymm
        (pair_mono (.impE h.allOpen.wk.wk Prf.hyp0) Prf.hyp1))
  simpa only [P, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using atBound

theorem sequence_mono (f g : PTm 2) (N x y : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift y)))) :
    Γ ⊢[PRAAx] le (sequence f N x) (sequence g N y) :=
  pair_mono (le_refl N) (stack_mono f g N x y h)

/-- Fixed bounded-verifier interface data. The observation relation may be
an equivalence bit or a query-indexed quantitative stability relation. -/
structure Interface where
  query : PR 2
  bound : PR 2
  verify : PR 3
  observe : PR 3
  related : PR 4

def valid (X : Interface) (c q p : PTm n) : Fm PTm n :=
  lt c (ap2 X.bound q p) ⋏ (ap3 X.verify c q p ≐ one)

def related (X : Interface) (c c' q p : PTm n) : Fm PTm n :=
  ap4 X.related (ap3 X.observe c q p) (ap3 X.observe c' q p) q p ≐ one

@[simp] theorem subst_valid {m : ℕ} (σ : Fin n → PTm m) (X : Interface) (c q p : PTm n) :
    (valid X c q p).subst σ = valid X (Syn.subst σ c) (Syn.subst σ q) (Syn.subst σ p) := by
  simp [valid]
ipra_subst related

theorem valid_congr (X : Interface) {c c' q q' p p' : PTm n}
    (hc : Γ ⊢[PRAAx] c ≐ c') (hq : Γ ⊢[PRAAx] q ≐ q') (hp : Γ ⊢[PRAAx] p ≐ p')
    (h : Γ ⊢[PRAAx] valid X c q p) : Γ ⊢[PRAAx] valid X c' q' p' := by
  have hs : Γ ⊢[PRAAx] (valid X (var 0) (var 1) (var 2)).subst ![c, q, p] := by simpa using h
  have out := Prf.eqSubst (valid X (var 0) (var 1) (var 2)) ![c, q, p] ![c', q', p']
    (fun i => by fin_cases i <;> assumption) hs
  simpa using out

#print axioms sequence_mono

/-! ## Canonical numerical master bounds and actual master validity -/

def capBody (X : Interface) : PTm 2 :=
  ap2 X.bound (entry (fstT (var 1)) (var 0)) (sndT (var 1))

def masterBound (X : Interface) (demands p : PTm n) : PTm n :=
  succ (sequence (capBody X) (length demands) (pairT demands p))

def masterValues (X : Interface) (demands C p : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift demands)) ⟶
    valid X (entry (Syn.shift C) (var 0)) (entry (Syn.shift demands) (var 0)) (Syn.shift p))

def masterValid (X : Interface) (demands C p : PTm n) : Fm PTm n :=
  lt C (masterBound X demands p) ⋏
    ((length C ≐ length demands) ⋏ masterValues X demands C p)

ipra_subst masterBound
@[simp] theorem subst_masterValues {m : ℕ} (σ : Fin n → PTm m) (X : Interface) (demands C p : PTm n) :
    (masterValues X demands C p).subst σ =
      masterValues X (Syn.subst σ demands) (Syn.subst σ C) (Syn.subst σ p) := by
  simp only [masterValues, Fm.subst_all, Fm.subst_imp, subst_lt, subst_valid,
    SequenceComposition.subst_length, MasterCertificate.subst_entry, Syn.subst_var,
    Syn.up_zero, Syn.subst_shift, Syn.shift_subst, Syn.up_succ]
@[simp] theorem subst_masterValid {m : ℕ} (σ : Fin n → PTm m) (X : Interface) (demands C p : PTm n) :
    (masterValid X demands C p).subst σ =
      masterValid X (Syn.subst σ demands) (Syn.subst σ C) (Syn.subst σ p) := by simp [masterValid]

theorem capBody_at (X : Interface) (demands p i : PTm n) :
    Γ ⊢[PRAAx] inst2 (capBody X) i (pairT demands p) ≐ ap2 X.bound (entry demands i) p := by
  simp only [capBody, inst2, subst_ap2, MasterCertificate.subst_entry,
    subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact congrAp2 X.bound (entry_congr (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

theorem master_values_at (X : Interface) {demands C p i : PTm n}
    (h : Γ ⊢[PRAAx] masterValues X demands C p) (hi : Γ ⊢[PRAAx] lt i (length demands)) :
    Γ ⊢[PRAAx] valid X (entry C i) (entry demands i) p := by
  have h' := Prf.allE i h
  simp only [masterValues, Fm.subst_imp, subst_lt, subst_valid, SequenceComposition.subst_length,
    MasterCertificate.subst_entry, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h'
  exact Prf.impE h' hi

/-- The exclusive bound is a computed canonical sequence of pointwise caps,
not an unproved estimate on an arbitrary stack representation. -/
theorem canonical_master (X : Interface) (f : PTm 2) (demands p x : PTm n)
    (h : Γ ⊢[PRAAx] .all (lt (var 0) (length (Syn.shift demands)) ⟶
      valid X (inst2 f (var 0) (Syn.shift x)) (entry (Syn.shift demands) (var 0)) (Syn.shift p))) :
    Γ ⊢[PRAAx] masterValid X demands (sequence f (length demands) x) p := by
  have bound : Γ ⊢[PRAAx]
      le (sequence f (length demands) x) (sequence (capBody X) (length demands) (pairT demands p)) := by
    apply sequence_mono
    refine .allI (.impI ?_)
    have atIndex := Prf.impE h.allOpen.wk Prf.hyp0
    have capped := le_of_lt (Prf.andE₁ atIndex)
    simpa only [Syn.shift, subst_pairT, SequenceComposition.subst_length] using
      le_congr (.eqRefl _) (capBody_at X (Syn.shift demands) (Syn.shift p) (var 0)).eqSymm capped
  refine .andI ((succ_monus_succ _ _).eqTrans bound) (.andI (sequence_length _ _ _) ?_)
  refine .allI (.impI ?_)
  have atIndex := Prf.impE h.allOpen.wk Prf.hyp0
  have decoded := sequence_decode f (x := Syn.shift x)
    (Prf.hyp0 : lt (var 0) (length (Syn.shift demands)) :: Γ.map Fm.shift ⊢[PRAAx] _)
  simpa only [Syn.shift, MasterCertificate.subst_sequence, SequenceComposition.subst_length] using
    valid_congr X decoded.eqSymm (.eqRefl _) (.eqRefl _) atIndex

/-! ## An actual PR submaster extractor -/

def sliceBody : PTm 2 := entry (sndT (var 1)) (fstT (var 1) + var 0)
def slice (C offset amount : PTm n) : PTm n := sequence sliceBody amount (pairT offset C)

ipra_subst slice

theorem sliceBody_at (C offset i : PTm n) :
    Γ ⊢[PRAAx] inst2 sliceBody i (pairT offset C) ≐ entry C (offset + i) := by
  simp only [sliceBody, inst2, MasterCertificate.subst_entry, subst_fstT, subst_sndT,
    PTm.subst_add, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact entry_congr (snd_pair _ _) (congrAdd (fst_pair _ _) (.eqRefl _))

theorem slice_length (C offset amount : PTm n) :
    Γ ⊢[PRAAx] length (slice C offset amount) ≐ amount := sequence_length _ _ _

theorem slice_lookup (C offset amount i : PTm n) (hi : Γ ⊢[PRAAx] lt i amount) :
    Γ ⊢[PRAAx] entry (slice C offset amount) i ≐ entry C (offset + i) :=
  (sequence_decode sliceBody hi).eqTrans (sliceBody_at _ _ _)

#print axioms canonical_master
#print axioms slice_lookup

theorem flat_offset_bound (inner : PR 2) (outer p j i : PTm n)
    (hj : Γ ⊢[PRAAx] lt j (length outer))
    (hi : Γ ⊢[PRAAx] lt i (length (block inner outer p j))) :
    Γ ⊢[PRAAx] lt (prefixSum inner outer p j + i) (length (flatMap inner outer p)) := by
  have localBound : Γ ⊢[PRAAx]
      lt (prefixSum inner outer p j + i) (prefixSum inner outer p (succ j)) :=
    lt_congr (.eqRefl _) (SequenceComposition.prefix_succ _ _ _ _).eqSymm
      (SequenceComposition.add_lt_left _ hi)
  have whole := lt_of_lt_of_le localBound (SequenceComposition.prefix_mono inner outer p hj)
  exact lt_congr (.eqRefl _) (flatMap_length _ _ _).eqSymm whole

/-- The extracted canonical submaster is valid by actual slice decoding and
actual flattened-demand decoding. Its numerical code bound is also derived. -/
theorem extracted_master_valid (X : Interface) (inner : PR 2) (outer C p j : PTm n)
    (hj : Γ ⊢[PRAAx] lt j (length outer))
    (hC : Γ ⊢[PRAAx] masterValid X (flatMap inner outer p) C p) :
    Γ ⊢[PRAAx] masterValid X (block inner outer p j)
      (slice C (prefixSum inner outer p j) (length (block inner outer p j))) p := by
  apply canonical_master
  refine .allI (.impI ?_)
  have shifted : Γ.map Fm.shift ⊢[PRAAx]
      masterValid X (flatMap inner (Syn.shift outer) (Syn.shift p)) (Syn.shift C) (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hC.shift
  have hjShift : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (length (Syn.shift outer)) := by
    simpa [Fm.shift, Syn.shift] using hj.shift
  have atIndex := master_values_at X (Prf.andE₂ (Prf.andE₂ shifted.wk))
    (flat_offset_bound inner (Syn.shift outer) (Syn.shift p) (Syn.shift j) (var 0) hjShift.wk Prf.hyp0)
  have queryEq := flatMap_lookup inner (Syn.shift outer) (Syn.shift p) (Syn.shift j) (var 0) hjShift.wk Prf.hyp0
  have certEq := sliceBody_at (Γ := lt (var 0) (length (block inner (Syn.shift outer) (Syn.shift p) (Syn.shift j))) ::
      Γ.map Fm.shift) (Syn.shift C) (prefixSum inner (Syn.shift outer) (Syn.shift p) (Syn.shift j)) (var 0)
  simpa only [Syn.shift, subst_pairT, SequenceComposition.subst_prefix,
    SequenceComposition.subst_block, SequenceComposition.subst_length] using
    valid_congr X certEq.eqSymm queryEq (.eqRefl _) atIndex

#print axioms extracted_master_valid

/-! ## An actual bounded PR master verifier and its reflection proof -/

def validityBit (X : Interface) (c q p : PTm n) : PTm n :=
  eqb (pairT (monus (succ c) (ap2 X.bound q p)) (ap3 X.verify c q p)) (pairT zero one)

ipra_subst validityBit

theorem validityBit_sound (X : Interface) (c q p : PTm n)
    (h : Γ ⊢[PRAAx] validityBit X c q p ≐ one) : Γ ⊢[PRAAx] valid X c q p := by
  have e := eq_of_eqb h
  exact .andI
    ((fst_pair _ _).eqSymm.eqTrans ((congrFst e).eqTrans (fst_pair _ _)))
    ((snd_pair _ _).eqSymm.eqTrans ((congrSnd e).eqTrans (snd_pair _ _)))

theorem validityBit_complete (X : Interface) (c q p : PTm n) (h : Γ ⊢[PRAAx] valid X c q p) :
    Γ ⊢[PRAAx] validityBit X c q p ≐ one :=
  eqb_of_eq (pair_congr (Prf.andE₁ h) (Prf.andE₂ h))

theorem validityBit_congr (X : Interface) {c c' q q' p p' : PTm n}
    (hc : Γ ⊢[PRAAx] c ≐ c') (hq : Γ ⊢[PRAAx] q ≐ q') (hp : Γ ⊢[PRAAx] p ≐ p') :
    Γ ⊢[PRAAx] validityBit X c q p ≐ validityBit X c' q' p' := by
  have h := Prf.eqCongr (Γ := Γ) (validityBit X (var 0) (var 1) (var 2))
    (σ := ![c, q, p]) (σ' := ![c', q', p']) (fun i => by fin_cases i <;> assumption)
  simpa using h

def masterBody (X : Interface) : PTm 2 :=
  validityBit X (entry (fstT (var 1)) (var 0))
    (entry (fstT (sndT (var 1))) (var 0)) (sndT (sndT (var 1)))

def masterCoordinateBit (X : Interface) (demands C p : PTm n) : PTm n :=
  allB (masterBody X) (length demands) (pairT C (pairT demands p))

ipra_subst masterCoordinateBit [allB]

theorem masterBody_at (X : Interface) (demands C p i : PTm n) :
    Γ ⊢[PRAAx] inst2 (masterBody X) i (pairT C (pairT demands p)) ≐
      validityBit X (entry C i) (entry demands i) p := by
  simp only [masterBody, inst2, subst_validityBit, MasterCertificate.subst_entry,
    subst_fstT, subst_sndT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact validityBit_congr X (entry_congr (fst_pair _ _) (.eqRefl _))
    (entry_congr ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)) (.eqRefl _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))

theorem coordinateBit_at (X : Interface) {demands C p i : PTm n}
    (h : Γ ⊢[PRAAx] masterCoordinateBit X demands C p ≐ one)
    (hi : Γ ⊢[PRAAx] lt i (length demands)) :
    Γ ⊢[PRAAx] valid X (entry C i) (entry demands i) p := by
  have nonzero := all_elim (masterBody X) h hi
  refine .orE (eqb_cases
    (pairT (monus (succ (entry C i)) (ap2 X.bound (entry demands i) p))
      (ap3 X.verify (entry C i) (entry demands i) p)) (pairT zero one)) ?_ ?_
  · exact .botE _ (.impE nonzero.wk ((masterBody_at X demands C p i).wk.eqTrans Prf.hyp0))
  · exact validityBit_sound X _ _ _ Prf.hyp0

theorem coordinateBit_sound (X : Interface) (demands C p : PTm n)
    (h : Γ ⊢[PRAAx] masterCoordinateBit X demands C p ≐ one) :
    Γ ⊢[PRAAx] masterValues X demands C p := by
  refine .allI (.impI ?_)
  have shifted : Γ.map Fm.shift ⊢[PRAAx]
      masterCoordinateBit X (Syn.shift demands) (Syn.shift C) (Syn.shift p) ≐ one := by
    simpa [Fm.shift, Syn.shift] using h.shift
  exact coordinateBit_at X shifted.wk Prf.hyp0

theorem coordinateBit_complete (X : Interface) (demands C p : PTm n)
    (h : Γ ⊢[PRAAx] masterValues X demands C p) :
    Γ ⊢[PRAAx] masterCoordinateBit X demands C p ≐ one := by
  apply all_intro
  refine .allI (.impI (.impI ?_))
  have shifted : Γ.map Fm.shift ⊢[PRAAx]
      masterValues X (Syn.shift demands) (Syn.shift C) (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using h.shift
  let Δ : List (Fm PTm (n + 1)) :=
    (inst2 (masterBody X) (var 0) (Syn.shift (pairT C (pairT demands p))) ≐ zero) ::
      lt (var 0) (Syn.shift (length demands)) :: Γ.map Fm.shift
  have indexBound : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift demands)) := by
    simpa only [Δ, Syn.shift, SequenceComposition.subst_length] using
      (Prf.hyp1 : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (length demands)))
  have accepted : Δ ⊢[PRAAx]
      validityBit X (entry (Syn.shift C) (var 0)) (entry (Syn.shift demands) (var 0)) (Syn.shift p) ≐ one :=
    validityBit_complete X _ _ _ (master_values_at X shifted.wk.wk indexBound)
  have one := (masterBody_at X (Syn.shift demands) (Syn.shift C) (Syn.shift p) (var 0)).eqTrans accepted
  have zero : (inst2 (masterBody X) (var 0) (Syn.shift (pairT C (pairT demands p))) ≐ zero) ::
      lt (var 0) (Syn.shift (length demands)) :: Γ.map Fm.shift ⊢[PRAAx]
      inst2 (masterBody X) (var 0) (pairT (Syn.shift C) (pairT (Syn.shift demands) (Syn.shift p))) ≐ zero := by
    simpa [Syn.shift, subst_pairT] using (Prf.hyp0 : _ ⊢[PRAAx] _)
  exact one_ne_zero _ (one.eqSymm.eqTrans zero)

def masterBit (X : Interface) (demands C p : PTm n) : PTm n :=
  eqb (pairT (monus (succ C) (masterBound X demands p))
      (pairT (length C) (masterCoordinateBit X demands C p)))
    (pairT zero (pairT (length demands) one))

ipra_subst masterBit

theorem masterBit_sound (X : Interface) (demands C p : PTm n)
    (h : Γ ⊢[PRAAx] masterBit X demands C p ≐ one) : Γ ⊢[PRAAx] masterValid X demands C p := by
  have e := eq_of_eqb h
  have tail := (snd_pair _ _).eqSymm.eqTrans ((congrSnd e).eqTrans (snd_pair _ _))
  have bound := (fst_pair _ _).eqSymm.eqTrans ((congrFst e).eqTrans (fst_pair _ _))
  have len := (fst_pair _ _).eqSymm.eqTrans ((congrFst tail).eqTrans (fst_pair _ _))
  have coordinates := (snd_pair _ _).eqSymm.eqTrans ((congrSnd tail).eqTrans (snd_pair _ _))
  exact .andI bound (.andI len (coordinateBit_sound X _ _ _ coordinates))

theorem masterBit_complete (X : Interface) (demands C p : PTm n)
    (h : Γ ⊢[PRAAx] masterValid X demands C p) : Γ ⊢[PRAAx] masterBit X demands C p ≐ one :=
  eqb_of_eq (pair_congr (Prf.andE₁ h)
    (pair_congr (Prf.andE₁ (Prf.andE₂ h)) (coordinateBit_complete X _ _ _ (Prf.andE₂ (Prf.andE₂ h)))))

def masterVerifierF (X : Interface) : PR 3 := PTm.toPR (masterBit X (var 1) (var 0) (var 2))

theorem masterVerifier_at (X : Interface) (demands C p : PTm n) :
    Γ ⊢[PRAAx] ap3 (masterVerifierF X) C demands p ≐ masterBit X demands C p := by
  have h := toPR_eq (Γ := Γ) (masterBit X (var 1) (var 0) (var 2)) ![C, demands, p]
  simpa [masterVerifierF, ap3] using h

#print axioms masterBit_sound
#print axioms masterBit_complete

/-! ## Explicit residual scope and checked realizer contracts -/

def allOf : List (Fm PTm n) → Fm PTm n
  | [] => zero ≐ zero
  | A :: rest => A ⋏ allOf rest

@[simp] theorem subst_allOf {m : ℕ} (σ : Fin n → PTm m) (As : List (Fm PTm n)) :
    (allOf As).subst σ = allOf (As.map (fun A => A.subst σ)) := by
  induction As with
  | nil => simp [allOf]
  | cons A rest ih => simp [allOf, ih]

theorem allOf_at_elim {k : ℕ} (As : List (Fm PTm k)) (σ : Fin k → PTm n)
    (h : Γ ⊢[PRAAx] (allOf As).subst σ) {A : Fm PTm k} (ha : A ∈ As) :
    Γ ⊢[PRAAx] A.subst σ := by
  induction As with
  | nil => exact False.elim (List.not_mem_nil ha)
  | cons B rest ih =>
    rcases List.mem_cons.1 ha with rfl | tail
    · exact Prf.andE₁ h
    · exact ih (Prf.andE₂ h) tail

theorem allOf_at_intro {k : ℕ} (As : List (Fm PTm k)) (σ : Fin k → PTm n)
    (h : ∀ A, A ∈ As → (Γ ⊢[PRAAx] A.subst σ)) : Γ ⊢[PRAAx] (allOf As).subst σ := by
  revert h
  induction As with
  | nil => intro h; exact .eqRefl _
  | cons A rest ih =>
    intro h
    exact .andI (h A (List.mem_cons_self)) (ih (fun B hb => h B (List.mem_cons_of_mem A hb)))

def queryAt (A : Fm PTm 2) (q p : PTm n) : Fm PTm n := A.subst ![q, p]

@[simp] theorem subst_queryAt {m : ℕ} (σ : Fin n → PTm m) (A : Fm PTm 2) (q p : PTm n) :
    (queryAt A q p).subst σ = queryAt A (Syn.subst σ q) (Syn.subst σ p) := by
  simp only [queryAt, Fm.subst_subst]
  congr 1
  funext i
  fin_cases i <;> rfl

def specializeAll (A : Fm PTm 2) (outer p : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift outer)) ⟶ queryAt A (entry (Syn.shift outer) (var 0)) (Syn.shift p))

@[simp] theorem subst_specializeAll {m : ℕ} (σ : Fin n → PTm m) (A : Fm PTm 2) (outer p : PTm n) :
    (specializeAll A outer p).subst σ = specializeAll A (Syn.subst σ outer) (Syn.subst σ p) := by
  simp only [specializeAll, Fm.subst_all, Fm.subst_imp, subst_lt, subst_queryAt,
    SequenceComposition.subst_length, MasterCertificate.subst_entry, Syn.subst_var,
    Syn.up_zero, Syn.subst_shift, Syn.shift_subst, Syn.up_succ]

theorem specialize_at (A : Fm PTm 2) {outer p j : PTm n}
    (h : Γ ⊢[PRAAx] specializeAll A outer p) (hj : Γ ⊢[PRAAx] lt j (length outer)) :
    Γ ⊢[PRAAx] queryAt A (entry outer j) p := by
  have one := Prf.allE j h
  simp only [specializeAll, Fm.subst_imp, subst_lt, subst_queryAt, SequenceComposition.subst_length,
    MasterCertificate.subst_entry, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at one
  exact Prf.impE one hj

def masterRelated (X : Interface) (demands C C' p : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift demands)) ⟶
    related X (entry (Syn.shift C) (var 0)) (entry (Syn.shift C') (var 0))
      (entry (Syn.shift demands) (var 0)) (Syn.shift p))

@[simp] theorem subst_masterRelated {m : ℕ} (σ : Fin n → PTm m) (X : Interface)
    (demands C C' p : PTm n) :
    (masterRelated X demands C C' p).subst σ = masterRelated X (Syn.subst σ demands)
      (Syn.subst σ C) (Syn.subst σ C') (Syn.subst σ p) := by
  simp only [masterRelated, Fm.subst_all, Fm.subst_imp, subst_lt, subst_related,
    SequenceComposition.subst_length, MasterCertificate.subst_entry, Syn.subst_var,
    Syn.up_zero, Syn.subst_shift, Syn.shift_subst, Syn.up_succ]

theorem master_related_at (X : Interface) {demands C C' p i : PTm n}
    (h : Γ ⊢[PRAAx] masterRelated X demands C C' p) (hi : Γ ⊢[PRAAx] lt i (length demands)) :
    Γ ⊢[PRAAx] related X (entry C i) (entry C' i) (entry demands i) p := by
  have one := Prf.allE i h
  simp only [masterRelated, Fm.subst_imp, subst_lt, subst_related, SequenceComposition.subst_length,
    MasterCertificate.subst_entry, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at one
  exact Prf.impE one hi

theorem related_congr (X : Interface) {c c' d d' q q' p p' : PTm n}
    (hc : Γ ⊢[PRAAx] c ≐ c') (hd : Γ ⊢[PRAAx] d ≐ d')
    (hq : Γ ⊢[PRAAx] q ≐ q') (hp : Γ ⊢[PRAAx] p ≐ p')
    (h : Γ ⊢[PRAAx] related X c d q p) : Γ ⊢[PRAAx] related X c' d' q' p' := by
  have source : Γ ⊢[PRAAx] (related X (var 0) (var 1) (var 2) (var 3)).subst ![c, d, q, p] := by
    simpa using h
  have out := Prf.eqSubst (related X (var 0) (var 1) (var 2) (var 3)) ![c, d, q, p] ![c', d', q', p']
    (fun i => by fin_cases i <;> assumption) source
  simpa using out

/-- Literal local sequents are inputs. Global composed soundness and
stability are derived from them, not supplied as fields. `guard` retains
well-formedness and any query-dependent precision/separation contract. -/
structure Realizer (X Y : Interface) where
  demand : PR 2
  transform : PR 3
  guard : Fm PTm 2
  residuals : List (Fm PTm 2)
  sound : [guard.shift, (allOf residuals).shift,
      masterValid X (ap2 demand (var 1) (var 2)) (var 0) (var 2)] ⊢[PRAAx]
    valid Y (ap3 transform (var 0) (var 1) (var 2)) (var 1) (var 2)
  stable : [guard.shift.shift, (allOf residuals).shift.shift,
      masterValid X (ap2 demand (var 2) (var 3)) (var 0) (var 3),
      masterValid X (ap2 demand (var 2) (var 3)) (var 1) (var 3),
      masterRelated X (ap2 demand (var 2) (var 3)) (var 0) (var 1) (var 3)] ⊢[PRAAx]
    related Y (ap3 transform (var 0) (var 2) (var 3))
      (ap3 transform (var 1) (var 2) (var 3)) (var 2) (var 3)

theorem cut3 {A B C D : Fm PTm n} (h : [A, B, C] ⊢[PRAAx] D)
    (ha : Γ ⊢[PRAAx] A) (hb : Γ ⊢[PRAAx] B) (hc : Γ ⊢[PRAAx] C) : Γ ⊢[PRAAx] D := by
  apply h.trans
  intro E he
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> assumption

theorem Realizer.applySound {X Y : Interface} (R : Realizer X Y) (C q p : PTm n)
    (hguard : Γ ⊢[PRAAx] queryAt R.guard q p) (hres : Γ ⊢[PRAAx] queryAt (allOf R.residuals) q p)
    (hmaster : Γ ⊢[PRAAx] masterValid X (ap2 R.demand q p) C p) :
    Γ ⊢[PRAAx] valid Y (ap3 R.transform C q p) q p := by
  have hLocal : [queryAt R.guard q p, queryAt (allOf R.residuals) q p,
      masterValid X (ap2 R.demand q p) C p] ⊢[PRAAx] valid Y (ap3 R.transform C q p) q p := by
    simpa [queryAt, Fm.shift, Syn.shift, Fm.subst_shift, Fm.subst_subst,
      Syn.subst_subst, Function.comp_def] using R.sound.subst ![C, q, p]
  exact cut3 hLocal hguard hres hmaster

#print axioms Realizer.applySound

theorem Realizer.applyStable {X Y : Interface} (R : Realizer X Y) (C C' q p : PTm n)
    (hguard : Γ ⊢[PRAAx] queryAt R.guard q p) (hres : Γ ⊢[PRAAx] queryAt (allOf R.residuals) q p)
    (hC : Γ ⊢[PRAAx] masterValid X (ap2 R.demand q p) C p)
    (hC' : Γ ⊢[PRAAx] masterValid X (ap2 R.demand q p) C' p)
    (hrel : Γ ⊢[PRAAx] masterRelated X (ap2 R.demand q p) C C' p) :
    Γ ⊢[PRAAx] related Y (ap3 R.transform C q p) (ap3 R.transform C' q p) q p := by
  have hLocal : [queryAt R.guard q p, queryAt (allOf R.residuals) q p,
      masterValid X (ap2 R.demand q p) C p, masterValid X (ap2 R.demand q p) C' p,
      masterRelated X (ap2 R.demand q p) C C' p] ⊢[PRAAx]
      related Y (ap3 R.transform C q p) (ap3 R.transform C' q p) q p := by
    simpa [queryAt, Fm.shift, Syn.shift, Fm.subst_shift, Fm.subst_subst,
      Syn.subst_subst, Function.comp_def] using R.stable.subst ![C, C', q, p]
  apply hLocal.trans
  intro E he
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem extracted_master_related (X : Interface) (inner : PR 2) (outer C C' p j : PTm n)
    (hj : Γ ⊢[PRAAx] lt j (length outer))
    (hrel : Γ ⊢[PRAAx] masterRelated X (flatMap inner outer p) C C' p) :
    Γ ⊢[PRAAx] masterRelated X (block inner outer p j)
      (slice C (prefixSum inner outer p j) (length (block inner outer p j)))
      (slice C' (prefixSum inner outer p j) (length (block inner outer p j))) p := by
  refine .allI (.impI ?_)
  have shifted : Γ.map Fm.shift ⊢[PRAAx]
      masterRelated X (flatMap inner (Syn.shift outer) (Syn.shift p))
        (Syn.shift C) (Syn.shift C') (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hrel.shift
  have hjShift : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (length (Syn.shift outer)) := by
    simpa [Fm.shift, Syn.shift] using hj.shift
  have point := master_related_at X shifted.wk
    (flat_offset_bound inner (Syn.shift outer) (Syn.shift p) (Syn.shift j) (var 0) hjShift.wk Prf.hyp0)
  have cEq := slice_lookup (Γ := lt (var 0) (length (block inner (Syn.shift outer) (Syn.shift p) (Syn.shift j))) ::
      Γ.map Fm.shift) (Syn.shift C) (prefixSum inner (Syn.shift outer) (Syn.shift p) (Syn.shift j))
      (length (block inner (Syn.shift outer) (Syn.shift p) (Syn.shift j))) (var 0) Prf.hyp0
  have cEq' := slice_lookup (Γ := lt (var 0) (length (block inner (Syn.shift outer) (Syn.shift p) (Syn.shift j))) ::
      Γ.map Fm.shift) (Syn.shift C') (prefixSum inner (Syn.shift outer) (Syn.shift p) (Syn.shift j))
      (length (block inner (Syn.shift outer) (Syn.shift p) (Syn.shift j))) (var 0) Prf.hyp0
  have qEq := flatMap_lookup inner (Syn.shift outer) (Syn.shift p) (Syn.shift j) (var 0) hjShift.wk Prf.hyp0
  simpa only [Syn.shift, subst_slice, SequenceComposition.subst_prefix,
    SequenceComposition.subst_block, SequenceComposition.subst_length] using
    related_congr X cEq.eqSymm cEq'.eqSymm qEq (.eqRefl _) point

/-! ## Compute R at every S query, then form a bounded actual Y master -/

def bundleValue {X Y : Interface} (R : Realizer X Y) (C outer p j : PTm n) : PTm n :=
  ap3 R.transform (slice C (prefixSum R.demand outer p j) (length (block R.demand outer p j)))
    (entry outer j) p

@[simp] theorem subst_bundleValue {m : ℕ} (σ : Fin n → PTm m) {X Y : Interface}
    (R : Realizer X Y) (C outer p j : PTm n) :
    Syn.subst σ (bundleValue R C outer p j) =
      bundleValue R (Syn.subst σ C) (Syn.subst σ outer) (Syn.subst σ p) (Syn.subst σ j) := by
  simp [bundleValue]

def bundleBody {X Y : Interface} (R : Realizer X Y) : PTm 2 :=
  bundleValue R (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)

def bundle {X Y : Interface} (R : Realizer X Y) (C outer p : PTm n) : PTm n :=
  sequence (bundleBody R) (length outer) (pairT C (pairT outer p))

ipra_subst bundle

theorem bundleBody_at {X Y : Interface} (R : Realizer X Y) (C outer p j : PTm n) :
    Γ ⊢[PRAAx] inst2 (bundleBody R) j (pairT C (pairT outer p)) ≐ bundleValue R C outer p j := by
  have h := Prf.eqCongr (Γ := Γ) (bundleValue R (var 0) (var 1) (var 2) (var 3))
    (σ := ![fstT (pairT C (pairT outer p)), fstT (sndT (pairT C (pairT outer p))),
      sndT (sndT (pairT C (pairT outer p))), j]) (σ' := ![C, outer, p, j]) (fun i => by
      fin_cases i
      · exact fst_pair _ _
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
      · exact .eqRefl _)
  simpa [bundleBody, inst2] using h

theorem bundle_lookup {X Y : Interface} (R : Realizer X Y) (C outer p j : PTm n)
    (hj : Γ ⊢[PRAAx] lt j (length outer)) :
    Γ ⊢[PRAAx] entry (bundle R C outer p) j ≐ bundleValue R C outer p j :=
  (sequence_decode (bundleBody R) hj).eqTrans (bundleBody_at _ _ _ _ _)

theorem bundle_valid {X Y : Interface} (R : Realizer X Y) (C outer p : PTm n)
    (hguard : Γ ⊢[PRAAx] specializeAll R.guard outer p)
    (hres : Γ ⊢[PRAAx] specializeAll (allOf R.residuals) outer p)
    (hC : Γ ⊢[PRAAx] masterValid X (flatMap R.demand outer p) C p) :
    Γ ⊢[PRAAx] masterValid Y outer (bundle R C outer p) p := by
  apply canonical_master
  refine .allI (.impI ?_)
  have guardShift : Γ.map Fm.shift ⊢[PRAAx] specializeAll R.guard (Syn.shift outer) (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hguard.shift
  have resShift : Γ.map Fm.shift ⊢[PRAAx] specializeAll (allOf R.residuals) (Syn.shift outer) (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hres.shift
  have masterShift : Γ.map Fm.shift ⊢[PRAAx]
      masterValid X (flatMap R.demand (Syn.shift outer) (Syn.shift p)) (Syn.shift C) (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hC.shift
  have atIndex := R.applySound
    (slice (Syn.shift C) (prefixSum R.demand (Syn.shift outer) (Syn.shift p) (var 0))
      (length (block R.demand (Syn.shift outer) (Syn.shift p) (var 0))))
    (entry (Syn.shift outer) (var 0)) (Syn.shift p)
    (specialize_at _ guardShift.wk Prf.hyp0) (specialize_at _ resShift.wk Prf.hyp0)
    (extracted_master_valid X R.demand _ _ _ _ Prf.hyp0 masterShift.wk)
  have codeEq := bundleBody_at (Γ := lt (var 0) (length (Syn.shift outer)) :: Γ.map Fm.shift)
    R (Syn.shift C) (Syn.shift outer) (Syn.shift p) (var 0)
  simpa only [Syn.shift, subst_pairT] using valid_congr Y codeEq.eqSymm (.eqRefl _) (.eqRefl _) atIndex

#print axioms bundle_valid

theorem bundle_related {X Y : Interface} (R : Realizer X Y) (C C' outer p : PTm n)
    (hguard : Γ ⊢[PRAAx] specializeAll R.guard outer p)
    (hres : Γ ⊢[PRAAx] specializeAll (allOf R.residuals) outer p)
    (hC : Γ ⊢[PRAAx] masterValid X (flatMap R.demand outer p) C p)
    (hC' : Γ ⊢[PRAAx] masterValid X (flatMap R.demand outer p) C' p)
    (hrel : Γ ⊢[PRAAx] masterRelated X (flatMap R.demand outer p) C C' p) :
    Γ ⊢[PRAAx] masterRelated Y outer (bundle R C outer p) (bundle R C' outer p) p := by
  refine .allI (.impI ?_)
  have guardShift : Γ.map Fm.shift ⊢[PRAAx] specializeAll R.guard (Syn.shift outer) (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hguard.shift
  have resShift : Γ.map Fm.shift ⊢[PRAAx] specializeAll (allOf R.residuals) (Syn.shift outer) (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hres.shift
  have masterShift : Γ.map Fm.shift ⊢[PRAAx]
      masterValid X (flatMap R.demand (Syn.shift outer) (Syn.shift p)) (Syn.shift C) (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hC.shift
  have masterShift' : Γ.map Fm.shift ⊢[PRAAx]
      masterValid X (flatMap R.demand (Syn.shift outer) (Syn.shift p)) (Syn.shift C') (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hC'.shift
  have relatedShift : Γ.map Fm.shift ⊢[PRAAx]
      masterRelated X (flatMap R.demand (Syn.shift outer) (Syn.shift p))
        (Syn.shift C) (Syn.shift C') (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hrel.shift
  have atIndex := R.applyStable
    (slice (Syn.shift C) (prefixSum R.demand (Syn.shift outer) (Syn.shift p) (var 0))
      (length (block R.demand (Syn.shift outer) (Syn.shift p) (var 0))))
    (slice (Syn.shift C') (prefixSum R.demand (Syn.shift outer) (Syn.shift p) (var 0))
      (length (block R.demand (Syn.shift outer) (Syn.shift p) (var 0))))
    (entry (Syn.shift outer) (var 0)) (Syn.shift p)
    (specialize_at _ guardShift.wk Prf.hyp0) (specialize_at _ resShift.wk Prf.hyp0)
    (extracted_master_valid X R.demand _ _ _ _ Prf.hyp0 masterShift.wk)
    (extracted_master_valid X R.demand _ _ _ _ Prf.hyp0 masterShift'.wk)
    (extracted_master_related X R.demand _ _ _ _ _ Prf.hyp0 relatedShift.wk)
  have cEq := bundle_lookup (Γ := lt (var 0) (length (Syn.shift outer)) :: Γ.map Fm.shift)
    R (Syn.shift C) (Syn.shift outer) (Syn.shift p) (var 0) Prf.hyp0
  have cEq' := bundle_lookup (Γ := lt (var 0) (length (Syn.shift outer)) :: Γ.map Fm.shift)
    R (Syn.shift C') (Syn.shift outer) (Syn.shift p) (var 0) Prf.hyp0
  simpa only [Syn.shift, subst_bundle] using
    related_congr Y cEq.eqSymm cEq'.eqSymm (.eqRefl _) (.eqRefl _) atIndex

/-! ## Exact guards, residual families, and composed primitive programs -/

def demandTerm {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) (q p : PTm n) : PTm n :=
  flatMap R.demand (ap2 S.demand q p) p

def demandF {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) : PR 2 :=
  PTm.toPR (demandTerm R S (var 0) (var 1))

ipra_subst demandTerm

theorem demand_at {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) (q p : PTm n) :
    Γ ⊢[PRAAx] ap2 (demandF R S) q p ≐ demandTerm R S q p := by
  have h := toPR_eq (Γ := Γ) (demandTerm R S (var 0) (var 1)) ![q, p]
  simpa [demandF, ap2] using h

def transformTerm {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) (C q p : PTm n) : PTm n :=
  ap3 S.transform (bundle R C (ap2 S.demand q p) p) q p

def transformF {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) : PR 3 :=
  PTm.toPR (transformTerm R S (var 0) (var 1) (var 2))

ipra_subst transformTerm

theorem transform_at {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) (C q p : PTm n) :
    Γ ⊢[PRAAx] ap3 (transformF R S) C q p ≐ transformTerm R S C q p := by
  have h := toPR_eq (Γ := Γ) (transformTerm R S (var 0) (var 1) (var 2)) ![C, q, p]
  simpa [transformF, ap3] using h

def compositeGuard {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) : Fm PTm 2 :=
  S.guard ⋏ specializeAll R.guard (ap2 S.demand (var 0) (var 1)) (var 1)

def residualTemplate {Y Z : Interface} (S : Realizer Y Z) (A : Fm PTm 2) : Fm PTm 2 :=
  specializeAll A (ap2 S.demand (var 0) (var 1)) (var 1)

/-- Every R residual keeps its own runtime specialization family. -/
def compositeResiduals {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) : List (Fm PTm 2) :=
  S.residuals ++ R.residuals.map (residualTemplate S)

theorem guard_parts {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) (q p : PTm n)
    (h : Γ ⊢[PRAAx] queryAt (compositeGuard R S) q p) :
    Γ ⊢[PRAAx] queryAt S.guard q p ⋏ specializeAll R.guard (ap2 S.demand q p) p := by
  simpa [queryAt, compositeGuard] using h

theorem residuals_S {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) (q p : PTm n)
    (h : Γ ⊢[PRAAx] queryAt (allOf (compositeResiduals R S)) q p) :
    Γ ⊢[PRAAx] queryAt (allOf S.residuals) q p := by
  apply allOf_at_intro S.residuals ![q, p]
  intro A hA
  exact allOf_at_elim (compositeResiduals R S) ![q, p] h (List.mem_append_left _ hA)

theorem residual_family {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) (q p : PTm n)
    (h : Γ ⊢[PRAAx] queryAt (allOf (compositeResiduals R S)) q p)
    {A : Fm PTm 2} (hA : A ∈ R.residuals) :
    Γ ⊢[PRAAx] specializeAll A (ap2 S.demand q p) p := by
  have member : residualTemplate S A ∈ compositeResiduals R S :=
    List.mem_append_right _ (List.mem_map.mpr ⟨A, hA, rfl⟩)
  have one := allOf_at_elim (compositeResiduals R S) ![q, p] h member
  simpa [residualTemplate] using one

theorem residuals_R {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) (q p : PTm n)
    (h : Γ ⊢[PRAAx] queryAt (allOf (compositeResiduals R S)) q p) :
    Γ ⊢[PRAAx] specializeAll (allOf R.residuals) (ap2 S.demand q p) p := by
  refine .allI (.impI ?_)
  apply allOf_at_intro R.residuals ![entry (Syn.shift (ap2 S.demand q p)) (var 0), Syn.shift p]
  intro A hA
  have family := residual_family R S q p h hA
  have shifted : Γ.map Fm.shift ⊢[PRAAx]
      specializeAll A (ap2 S.demand (Syn.shift q) (Syn.shift p)) (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using family.shift
  simpa only [queryAt, Syn.shift, subst_ap2] using specialize_at A shifted.wk Prf.hyp0

theorem masterValid_congr (X : Interface) {demands demands' C C' p p' : PTm n}
    (hd : Γ ⊢[PRAAx] demands ≐ demands') (hc : Γ ⊢[PRAAx] C ≐ C') (hp : Γ ⊢[PRAAx] p ≐ p')
    (h : Γ ⊢[PRAAx] masterValid X demands C p) : Γ ⊢[PRAAx] masterValid X demands' C' p' := by
  have source : Γ ⊢[PRAAx] (masterValid X (var 0) (var 1) (var 2)).subst ![demands, C, p] := by simpa using h
  have out := Prf.eqSubst (masterValid X (var 0) (var 1) (var 2)) ![demands, C, p] ![demands', C', p']
    (fun i => by fin_cases i <;> assumption) source
  simpa using out

theorem masterRelated_congr (X : Interface) {demands demands' C C' D D' p p' : PTm n}
    (hd : Γ ⊢[PRAAx] demands ≐ demands') (hc : Γ ⊢[PRAAx] C ≐ C')
    (hD : Γ ⊢[PRAAx] D ≐ D') (hp : Γ ⊢[PRAAx] p ≐ p')
    (h : Γ ⊢[PRAAx] masterRelated X demands C D p) : Γ ⊢[PRAAx] masterRelated X demands' C' D' p' := by
  have source : Γ ⊢[PRAAx] (masterRelated X (var 0) (var 1) (var 2) (var 3)).subst ![demands, C, D, p] := by simpa using h
  have out := Prf.eqSubst (masterRelated X (var 0) (var 1) (var 2) (var 3))
    ![demands, C, D, p] ![demands', C', D', p'] (fun i => by fin_cases i <;> assumption) source
  simpa using out

theorem composed_sound {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) (C q p : PTm n)
    (hguard : Γ ⊢[PRAAx] queryAt (compositeGuard R S) q p)
    (hres : Γ ⊢[PRAAx] queryAt (allOf (compositeResiduals R S)) q p)
    (hC : Γ ⊢[PRAAx] masterValid X (ap2 (demandF R S) q p) C p) :
    Γ ⊢[PRAAx] valid Z (ap3 (transformF R S) C q p) q p := by
  have guards := guard_parts R S q p hguard
  have input := masterValid_congr X (demand_at R S q p) (.eqRefl _) (.eqRefl _) hC
  have intermediate := bundle_valid R C (ap2 S.demand q p) p
    (Prf.andE₂ guards) (residuals_R R S q p hres) input
  have output := S.applySound (bundle R C (ap2 S.demand q p) p) q p
    (Prf.andE₁ guards) (residuals_S R S q p hres) intermediate
  exact valid_congr Z (transform_at R S C q p).eqSymm (.eqRefl _) (.eqRefl _) output

theorem composed_stable {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) (C C' q p : PTm n)
    (hguard : Γ ⊢[PRAAx] queryAt (compositeGuard R S) q p)
    (hres : Γ ⊢[PRAAx] queryAt (allOf (compositeResiduals R S)) q p)
    (hC : Γ ⊢[PRAAx] masterValid X (ap2 (demandF R S) q p) C p)
    (hC' : Γ ⊢[PRAAx] masterValid X (ap2 (demandF R S) q p) C' p)
    (hrel : Γ ⊢[PRAAx] masterRelated X (ap2 (demandF R S) q p) C C' p) :
    Γ ⊢[PRAAx] related Z (ap3 (transformF R S) C q p) (ap3 (transformF R S) C' q p) q p := by
  have guards := guard_parts R S q p hguard
  have rres := residuals_R R S q p hres
  have input := masterValid_congr X (demand_at R S q p) (.eqRefl _) (.eqRefl _) hC
  have input' := masterValid_congr X (demand_at R S q p) (.eqRefl _) (.eqRefl _) hC'
  have relation := masterRelated_congr X (demand_at R S q p) (.eqRefl _) (.eqRefl _) (.eqRefl _) hrel
  have intermediate := bundle_valid R C (ap2 S.demand q p) p (Prf.andE₂ guards) rres input
  have intermediate' := bundle_valid R C' (ap2 S.demand q p) p (Prf.andE₂ guards) rres input'
  have relatedIntermediate := bundle_related R C C' (ap2 S.demand q p) p (Prf.andE₂ guards) rres input input' relation
  have output := S.applyStable (bundle R C (ap2 S.demand q p) p) (bundle R C' (ap2 S.demand q p) p) q p
    (Prf.andE₁ guards) (residuals_S R S q p hres) intermediate intermediate' relatedIntermediate
  exact related_congr Z (transform_at R S C q p).eqSymm (transform_at R S C' q p).eqSymm
    (.eqRefl _) (.eqRefl _) output

#print axioms composed_sound
#print axioms composed_stable

theorem queryAt_shift3 (A : Fm PTm 2) : queryAt A (var 1 : PTm 3) (var 2) = A.shift := by
  unfold queryAt Fm.shift
  congr 1
  funext i
  fin_cases i <;> rfl

theorem queryAt_shift4 (A : Fm PTm 2) : queryAt A (var 2 : PTm 4) (var 3) = A.shift.shift := by
  simp only [queryAt, Fm.shift, Fm.subst_subst]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Compose the actual bounded finite-query programs and their literal local
proof contracts. Every intermediate certificate is computed and kept local. -/
def compose {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) : Realizer X Z where
  demand := demandF R S
  transform := transformF R S
  guard := compositeGuard R S
  residuals := compositeResiduals R S
  sound := by
    let Δ : List (Fm PTm 3) := [(compositeGuard R S).shift, (allOf (compositeResiduals R S)).shift,
      masterValid X (ap2 (demandF R S) (var 1) (var 2)) (var 0) (var 2)]
    have hg : Δ ⊢[PRAAx] queryAt (compositeGuard R S) (var 1) (var 2) := by
      rw [queryAt_shift3]
      exact Prf.hyp0
    have hr : Δ ⊢[PRAAx] queryAt (allOf (compositeResiduals R S)) (var 1) (var 2) := by
      rw [queryAt_shift3]
      exact Prf.hyp1
    exact composed_sound R S (var 0) (var 1) (var 2) hg hr hyp2
  stable := by
    let Δ : List (Fm PTm 4) := [(compositeGuard R S).shift.shift, (allOf (compositeResiduals R S)).shift.shift,
      masterValid X (ap2 (demandF R S) (var 2) (var 3)) (var 0) (var 3),
      masterValid X (ap2 (demandF R S) (var 2) (var 3)) (var 1) (var 3),
      masterRelated X (ap2 (demandF R S) (var 2) (var 3)) (var 0) (var 1) (var 3)]
    have hg : Δ ⊢[PRAAx] queryAt (compositeGuard R S) (var 2) (var 3) := by
      rw [queryAt_shift4]
      exact Prf.hyp0
    have hr : Δ ⊢[PRAAx] queryAt (allOf (compositeResiduals R S)) (var 2) (var 3) := by
      rw [queryAt_shift4]
      exact Prf.hyp1
    exact composed_stable R S (var 0) (var 1) (var 2) (var 3) hg hr hyp2 hyp2.wk hyp2.wk.wk

/-! ## Explicit bound, verifier and observation programs for every realizer -/

def Realizer.inputBoundF {X Y : Interface} (R : Realizer X Y) : PR 2 :=
  PTm.toPR (masterBound X (ap2 R.demand (var 0) (var 1)) (var 1))

def Realizer.inputVerifierF {X Y : Interface} (R : Realizer X Y) : PR 3 :=
  PTm.toPR (masterBit X (ap2 R.demand (var 1) (var 2)) (var 0) (var 2))

def Realizer.outputObservationF {X Y : Interface} (R : Realizer X Y) : PR 3 :=
  PTm.toPR (ap3 Y.observe (ap3 R.transform (var 0) (var 1) (var 2)) (var 1) (var 2))

theorem Realizer.inputBound_at {X Y : Interface} (R : Realizer X Y) (q p : PTm n) :
    Γ ⊢[PRAAx] ap2 R.inputBoundF q p ≐ masterBound X (ap2 R.demand q p) p := by
  have h := toPR_eq (Γ := Γ) (masterBound X (ap2 R.demand (var 0) (var 1)) (var 1)) ![q, p]
  have clean : Γ ⊢[PRAAx] app R.inputBoundF ![q, p] ≐ masterBound X (ap2 R.demand q p) p := by
    simpa only [Realizer.inputBoundF, subst_masterBound, subst_ap2, Syn.subst_var,
      Matrix.cons_val_zero, Matrix.cons_val_one] using h
  simpa only [ap2] using clean

theorem Realizer.inputVerifier_at {X Y : Interface} (R : Realizer X Y) (C q p : PTm n) :
    Γ ⊢[PRAAx] ap3 R.inputVerifierF C q p ≐ masterBit X (ap2 R.demand q p) C p := by
  have h := toPR_eq (Γ := Γ) (masterBit X (ap2 R.demand (var 1) (var 2)) (var 0) (var 2)) ![C, q, p]
  simpa [Realizer.inputVerifierF, ap3] using h

theorem Realizer.outputObservation_at {X Y : Interface} (R : Realizer X Y) (C q p : PTm n) :
    Γ ⊢[PRAAx] ap3 R.outputObservationF C q p ≐ ap3 Y.observe (ap3 R.transform C q p) q p := by
  have h := toPR_eq (Γ := Γ) (ap3 Y.observe (ap3 R.transform (var 0) (var 1) (var 2)) (var 1) (var 2)) ![C, q, p]
  have clean : Γ ⊢[PRAAx] app R.outputObservationF ![C, q, p] ≐
      ap3 Y.observe (ap3 R.transform C q p) q p := by
    simpa only [Realizer.outputObservationF, subst_ap3, Syn.subst_var, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using h
  simpa only [ap3] using clean

theorem Realizer.verifier_sound {X Y : Interface} (R : Realizer X Y) (C q p : PTm n)
    (h : Γ ⊢[PRAAx] ap3 R.inputVerifierF C q p ≐ one) :
    Γ ⊢[PRAAx] masterValid X (ap2 R.demand q p) C p :=
  masterBit_sound X _ _ _ ((R.inputVerifier_at C q p).eqSymm.eqTrans h)

theorem Realizer.verifier_complete {X Y : Interface} (R : Realizer X Y) (C q p : PTm n)
    (h : Γ ⊢[PRAAx] masterValid X (ap2 R.demand q p) C p) :
    Γ ⊢[PRAAx] ap3 R.inputVerifierF C q p ≐ one :=
  (R.inputVerifier_at C q p).eqTrans (masterBit_complete X _ _ _ h)

theorem Realizer.verifier_cases {X Y : Interface} (R : Realizer X Y) (C q p : PTm n) :
    Γ ⊢[PRAAx] (ap3 R.inputVerifierF C q p ≐ zero) ⋎ (ap3 R.inputVerifierF C q p ≐ one) := by
  refine .orE (eqb_cases
    (pairT (monus (succ C) (masterBound X (ap2 R.demand q p) p))
      (pairT (length C) (masterCoordinateBit X (ap2 R.demand q p) C p)))
    (pairT zero (pairT (length (ap2 R.demand q p)) one)))
    (.orI₁ ((R.inputVerifier_at _ _ _).eqTrans Prf.hyp0))
    (.orI₂ ((R.inputVerifier_at _ _ _).eqTrans Prf.hyp0))

/-- The public observation program preserves exactly the declared output
relation, including whatever precision dependence the local guard retains. -/
theorem Realizer.observe_stable {X Y : Interface} (R : Realizer X Y) (C C' q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt R.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf R.residuals) q p)
    (hC : Γ ⊢[PRAAx] masterValid X (ap2 R.demand q p) C p)
    (hC' : Γ ⊢[PRAAx] masterValid X (ap2 R.demand q p) C' p)
    (hrel : Γ ⊢[PRAAx] masterRelated X (ap2 R.demand q p) C C' p) :
    Γ ⊢[PRAAx] ap4 Y.related (ap3 R.outputObservationF C q p)
      (ap3 R.outputObservationF C' q p) q p ≐ one := by
  have e : Γ ⊢[PRAAx] ap4 Y.related (ap3 R.outputObservationF C q p)
      (ap3 R.outputObservationF C' q p) q p ≐
      ap4 Y.related (ap3 Y.observe (ap3 R.transform C q p) q p)
        (ap3 Y.observe (ap3 R.transform C' q p) q p) q p :=
    congrApp Y.related (fun i => by
      fin_cases i
      · exact R.outputObservation_at C q p
      · exact R.outputObservation_at C' q p
      · exact .eqRefl _
      · exact .eqRefl _)
  exact e.eqTrans (R.applyStable C C' q p hg hr hC hC' hrel)

#print axioms compose
#print axioms Realizer.observe_stable

/-! ## Lexically seal input master witnesses -/

def inputTotal {X Y : Interface} (R : Realizer X Y) (q p : PTm n) : Fm PTm n :=
  .ex (ap3 R.inputVerifierF (var 0) (Syn.shift q) (Syn.shift p) ≐ one)

def outputTotal (Y : Interface) (q p : PTm n) : Fm PTm n :=
  .ex (valid Y (var 0) (Syn.shift q) (Syn.shift p))

theorem Realizer.seal {X Y : Interface} (R : Realizer X Y) (q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt R.guard q p) (hr : Γ ⊢[PRAAx] queryAt (allOf R.residuals) q p)
    (htotal : Γ ⊢[PRAAx] inputTotal R q p) : Γ ⊢[PRAAx] outputTotal Y q p := by
  refine Prf.exE htotal ?_
  have guardShift : Γ.map Fm.shift ⊢[PRAAx] queryAt R.guard (Syn.shift q) (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hg.shift
  have residualShift : Γ.map Fm.shift ⊢[PRAAx] queryAt (allOf R.residuals) (Syn.shift q) (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hr.shift
  let Δ : List (Fm PTm (n + 1)) :=
    (ap3 R.inputVerifierF (var 0) (Syn.shift q) (Syn.shift p) ≐ one) :: Γ.map Fm.shift
  have output : Δ ⊢[PRAAx] valid Y (ap3 R.transform (var 0) (Syn.shift q) (Syn.shift p)) (Syn.shift q) (Syn.shift p) :=
    R.applySound _ _ _ guardShift.wk residualShift.wk (R.verifier_sound _ _ _ Prf.hyp0)
  have sealed : Δ ⊢[PRAAx] .ex (valid Y (var 0) (Syn.shift (Syn.shift q)) (Syn.shift (Syn.shift p))) :=
    .exI (ap3 R.transform (var 0) (Syn.shift q) (Syn.shift p)) (by
      simpa only [subst_valid, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using output)
  simpa only [Δ, outputTotal, Fm.shift, Fm.subst_ex, subst_valid, Syn.subst_var,
    Syn.up_zero, Syn.subst_shift, Syn.shift_subst, Syn.up_succ, Syn.shift, Syn.subst_subst] using sealed

/-- An optional, separately checked certificate-independence contract.
The general composition constructor instead preserves the declared input-to-output
relation through each realizer's local stability theorem. -/
structure ObservationInvariant (X : Interface) where
  proof : [valid X (var 0 : PTm 4) (var 2) (var 3), valid X (var 1) (var 2) (var 3)] ⊢[PRAAx]
    related X (var 0) (var 1) (var 2) (var 3)

theorem ObservationInvariant.apply {X : Interface} (law : ObservationInvariant X) (c c' q p : PTm n)
    (hc : Γ ⊢[PRAAx] valid X c q p) (hc' : Γ ⊢[PRAAx] valid X c' q p) :
    Γ ⊢[PRAAx] related X c c' q p := by
  have hLocal : [valid X c q p, valid X c' q p] ⊢[PRAAx] related X c c' q p := by
    simpa using law.proof.subst ![c, c', q, p]
  apply hLocal.trans
  intro A hA
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl <;> assumption

theorem Realizer.certificate_independent {X Y : Interface} (R : Realizer X Y) (law : ObservationInvariant Y)
    (C C' q p : PTm n) (hg : Γ ⊢[PRAAx] queryAt R.guard q p)
    (hr : Γ ⊢[PRAAx] queryAt (allOf R.residuals) q p)
    (hC : Γ ⊢[PRAAx] masterValid X (ap2 R.demand q p) C p)
    (hC' : Γ ⊢[PRAAx] masterValid X (ap2 R.demand q p) C' p) :
    Γ ⊢[PRAAx] related Y (ap3 R.transform C q p) (ap3 R.transform C' q p) q p :=
  law.apply _ _ _ _ (R.applySound _ _ _ hg hr hC) (R.applySound _ _ _ hg hr hC')

/-! ## Closed theorem schemas for reuse under arbitrary terms and contexts -/

/-- Variables `0=C`, `1=q`, `2=p`. -/
def verifierFormula {X Y : Interface} (R : Realizer X Y) : Fm PTm 3 :=
  ((ap3 R.inputVerifierF (var 0) (var 1) (var 2) ≐ zero) ⋎
    (ap3 R.inputVerifierF (var 0) (var 1) (var 2) ≐ one)) ⋏
  (((ap3 R.inputVerifierF (var 0) (var 1) (var 2) ≐ one) ⟶
      masterValid X (ap2 R.demand (var 1) (var 2)) (var 0) (var 2)) ⋏
    (masterValid X (ap2 R.demand (var 1) (var 2)) (var 0) (var 2) ⟶
      (ap3 R.inputVerifierF (var 0) (var 1) (var 2) ≐ one)))

theorem bounded_master_verifier {X Y : Interface} (R : Realizer X Y) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (verifierFormula R) :=
  closeUniv 3 (.andI (R.verifier_cases _ _ _) (.andI
    (.impI (R.verifier_sound _ _ _ Prf.hyp0)) (.impI (R.verifier_complete _ _ _ Prf.hyp0))))

/-- Variables `0=C`, `1=q`, `2=p`. -/
def soundFormula {X Y : Interface} (R : Realizer X Y) : Fm PTm 3 :=
  queryAt R.guard (var 1) (var 2) ⟶ queryAt (allOf R.residuals) (var 1) (var 2) ⟶
    (ap3 R.inputVerifierF (var 0) (var 1) (var 2) ≐ one) ⟶
      valid Y (ap3 R.transform (var 0) (var 1) (var 2)) (var 1) (var 2)

theorem bounded_realizer_soundness {X Y : Interface} (R : Realizer X Y) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (soundFormula R) :=
  closeUniv 3 (.impI (.impI (.impI
    (R.applySound _ _ _ hyp2 Prf.hyp1 (R.verifier_sound _ _ _ Prf.hyp0)))))

/-- Variables `0=C`, `1=C'`, `2=q`, `3=p`. The actual output
observation program respects the exact chosen interface relation. -/
def stabilityFormula {X Y : Interface} (R : Realizer X Y) : Fm PTm 4 :=
  queryAt R.guard (var 2) (var 3) ⟶ queryAt (allOf R.residuals) (var 2) (var 3) ⟶
  (ap3 R.inputVerifierF (var 0) (var 2) (var 3) ≐ one) ⟶
  (ap3 R.inputVerifierF (var 1) (var 2) (var 3) ≐ one) ⟶
  masterRelated X (ap2 R.demand (var 2) (var 3)) (var 0) (var 1) (var 3) ⟶
    (ap4 Y.related (ap3 R.outputObservationF (var 0) (var 2) (var 3))
      (ap3 R.outputObservationF (var 1) (var 2) (var 3)) (var 2) (var 3) ≐ one)

theorem bounded_realizer_stability {X Y : Interface} (R : Realizer X Y) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (stabilityFormula R) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI
    (R.observe_stable _ _ _ _ hyp2.wk.wk hyp2.wk
      (R.verifier_sound _ _ _ hyp2) (R.verifier_sound _ _ _ Prf.hyp1) Prf.hyp0))))))

/-- Variables `0=q`, `1=p`. No input or intermediate master variable escapes. -/
def sealedFormula {X Y : Interface} (R : Realizer X Y) : Fm PTm 2 :=
  queryAt R.guard (var 0) (var 1) ⟶ queryAt (allOf R.residuals) (var 0) (var 1) ⟶
    inputTotal R (var 0) (var 1) ⟶ outputTotal Y (var 0) (var 1)

theorem bounded_realizer_sealed {X Y : Interface} (R : Realizer X Y) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (sealedFormula R) :=
  closeUniv 2 (.impI (.impI (.impI (R.seal _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem fiber_realizer_composition {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (soundFormula (compose R S)) :=
  bounded_realizer_soundness (compose R S)

theorem fiber_realizer_composition_stable {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (stabilityFormula (compose R S)) :=
  bounded_realizer_stability (compose R S)

theorem fiber_realizer_composition_sealed {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (sealedFormula (compose R S)) :=
  bounded_realizer_sealed (compose R S)

/-- Variables `0=C`, `1=q`, `2=p`: all generated metadata are actual PR programs. -/
def metadataFormula {X Y : Interface} (R : Realizer X Y) : Fm PTm 3 :=
  (ap2 R.inputBoundF (var 1) (var 2) ≐ masterBound X (ap2 R.demand (var 1) (var 2)) (var 2)) ⋏
    ((ap3 R.inputVerifierF (var 0) (var 1) (var 2) ≐ masterBit X
      (ap2 R.demand (var 1) (var 2)) (var 0) (var 2)) ⋏
      (ap3 R.outputObservationF (var 0) (var 1) (var 2) ≐
        ap3 Y.observe (ap3 R.transform (var 0) (var 1) (var 2)) (var 1) (var 2)))

theorem realizer_program_metadata {X Y : Interface} (R : Realizer X Y) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (metadataFormula R) :=
  closeUniv 3 (.andI (R.inputBound_at _ _) (.andI (R.inputVerifier_at _ _ _) (R.outputObservation_at _ _ _)))

/-- Variables `0=C`, `1=q`, `2=p`. -/
def compositionProgramsFormula {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) : Fm PTm 3 :=
  (ap2 (compose R S).demand (var 1) (var 2) ≐ flatMap R.demand
    (ap2 S.demand (var 1) (var 2)) (var 2)) ⋏
  ((ap3 (compose R S).transform (var 0) (var 1) (var 2) ≐
    ap3 S.transform (bundle R (var 0) (ap2 S.demand (var 1) (var 2)) (var 2)) (var 1) (var 2)) ⋏
    metadataFormula (compose R S))

theorem fiber_composition_programs {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (compositionProgramsFormula R S) :=
  closeUniv 3 (.andI (demand_at R S _ _) (.andI (transform_at R S _ _ _)
    (.andI ((compose R S).inputBound_at _ _) (.andI ((compose R S).inputVerifier_at _ _ _)
      ((compose R S).outputObservation_at _ _ _)))))

/-- Variables `0=outer`, `1=C`, `2=p`, `3=j`. -/
def extractionFormula (X : Interface) (inner : PR 2) : Fm PTm 4 :=
  lt (var 3) (length (var 0)) ⟶ masterValid X (flatMap inner (var 0) (var 2)) (var 1) (var 2) ⟶
    masterValid X (block inner (var 0) (var 2) (var 3))
      (slice (var 1) (prefixSum inner (var 0) (var 2) (var 3))
        (length (block inner (var 0) (var 2) (var 3)))) (var 2)

theorem checked_submaster_extraction (X : Interface) (inner : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (extractionFormula X inner) :=
  closeUniv 4 (.impI (.impI (extracted_master_valid X inner _ _ _ _ Prf.hyp1 Prf.hyp0)))

/-- The exact named residual list, with the persistent parameter left bound
at each original target query and each demanded intermediate query. -/
def residualContext {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) (q p : PTm n) : List (Fm PTm n) :=
  (compositeResiduals R S).map (fun A => queryAt A q p)

theorem fiber_composition_sequent {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) (C q p : PTm n) :
    (residualContext R S q p ++ [queryAt (compositeGuard R S) q p,
      ap3 (compose R S).inputVerifierF C q p ≐ one]) ⊢[PRAAx]
        valid Z (ap3 (compose R S).transform C q p) q p := by
  apply (compose R S).applySound C q p
  · exact .hyp (List.mem_append_right _ (List.mem_cons_self))
  · apply allOf_at_intro (compositeResiduals R S) ![q, p]
    intro A hA
    exact .hyp (List.mem_append_left _ (List.mem_map.mpr ⟨A, hA, rfl⟩))
  · apply (compose R S).verifier_sound C q p
    exact .hyp (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

theorem fiber_composition_sealed_sequent {X Y Z : Interface} (R : Realizer X Y) (S : Realizer Y Z) (q p : PTm n) :
    (residualContext R S q p ++ [queryAt (compositeGuard R S) q p, inputTotal (compose R S) q p]) ⊢[PRAAx]
      outputTotal Z q p := by
  apply (compose R S).seal q p
  · exact .hyp (List.mem_append_right _ (List.mem_cons_self))
  · apply allOf_at_intro (compositeResiduals R S) ![q, p]
    intro A hA
    exact .hyp (List.mem_append_left _ (List.mem_map.mpr ⟨A, hA, rfl⟩))
  · exact .hyp (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

/-- Variables `0=C`, `1=C'`, `2=q`, `3=p`. Certificate independence
requires the separately checked output-interface law; it is not assumed
merely because the transformer returns a certificate. -/
def independenceFormula {X Y : Interface} (R : Realizer X Y) : Fm PTm 4 :=
  queryAt R.guard (var 2) (var 3) ⟶ queryAt (allOf R.residuals) (var 2) (var 3) ⟶
    (ap3 R.inputVerifierF (var 0) (var 2) (var 3) ≐ one) ⟶
    (ap3 R.inputVerifierF (var 1) (var 2) (var 3) ≐ one) ⟶
      related Y (ap3 R.transform (var 0) (var 2) (var 3))
        (ap3 R.transform (var 1) (var 2) (var 3)) (var 2) (var 3)

theorem realizer_certificate_independence {X Y : Interface} (R : Realizer X Y) (law : ObservationInvariant Y) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (independenceFormula R) :=
  closeUniv 4 (.impI (.impI (.impI (.impI
    (R.certificate_independent law _ _ _ _ hyp2.wk hyp2
      (R.verifier_sound _ _ _ Prf.hyp1) (R.verifier_sound _ _ _ Prf.hyp0))))))

#print axioms Realizer.seal
#print axioms bounded_master_verifier
#print axioms fiber_realizer_composition
#print axioms fiber_realizer_composition_stable
#print axioms fiber_realizer_composition_sealed
#print axioms realizer_program_metadata
#print axioms fiber_composition_programs
#print axioms checked_submaster_extraction
#print axioms fiber_composition_sequent
#print axioms fiber_composition_sealed_sequent
#print axioms realizer_certificate_independence

end LeanProofs.IPRA.Foundations.RealizerComposition
