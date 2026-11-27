import IPRADerivations.Foundations.RealizerComposition

/-!
# Binary product interfaces and actual bounded fanout realizers

Product queries decode as pairs; certificates and observations are constructed
with the checked `pairT`. The product verifier checks both decoded component
certificate bounds and verifiers. The exclusive product cap is one plus the
actual pair of component caps. Its observation relation checks the two
component relations.

Fanout appends both demand lists, extracts canonical bounded submasters from
the actual input master, executes both child transformers, and pairs their
outputs. All query specializations retain the persistent parameter `p`.
Projection realizers request one actual paired query, with an explicit PR
selector for the unused component, and return its decoded certificate.
The interface is the fixed PR data projection; optional component
certificate-independence laws separately induce the product law below.
This is the binary pair-node arithmetic for the bounded acyclic frontend;
it does not translate the remaining FIBER source node kinds or cyclic graphs.
-/

namespace LeanProofs.IPRA.Foundations.RealizerProduct

open_ipra exports
open LeanProofs.IPRA.Foundations.RealizerComposition
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence entry sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition
  (length append append_length append_left append_right entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def queryTerm (Y Z : Interface) (q p : PTm n) : PTm n :=
  eqb (pairT (ap2 Y.query (fstT q) p) (ap2 Z.query (sndT q) p)) (pairT one one)

def boundTerm (Y Z : Interface) (q p : PTm n) : PTm n :=
  succ (pairT (ap2 Y.bound (fstT q) p) (ap2 Z.bound (sndT q) p))

def verifyTerm (Y Z : Interface) (c q p : PTm n) : PTm n :=
  eqb (pairT (validityBit Y (fstT c) (fstT q) p) (validityBit Z (sndT c) (sndT q) p)) (pairT one one)

def observeTerm (Y Z : Interface) (c q p : PTm n) : PTm n :=
  pairT (ap3 Y.observe (fstT c) (fstT q) p) (ap3 Z.observe (sndT c) (sndT q) p)

def relationTerm (Y Z : Interface) (o o' q p : PTm n) : PTm n :=
  eqb (pairT (ap4 Y.related (fstT o) (fstT o') (fstT q) p)
    (ap4 Z.related (sndT o) (sndT o') (sndT q) p)) (pairT one one)

ipra_subst queryTerm
ipra_subst boundTerm
ipra_subst verifyTerm
ipra_subst observeTerm
ipra_subst relationTerm

def product (Y Z : Interface) : Interface where
  query := PTm.toPR (queryTerm Y Z (var 0) (var 1))
  bound := PTm.toPR (boundTerm Y Z (var 0) (var 1))
  verify := PTm.toPR (verifyTerm Y Z (var 0) (var 1) (var 2))
  observe := PTm.toPR (observeTerm Y Z (var 0) (var 1) (var 2))
  related := PTm.toPR (relationTerm Y Z (var 0) (var 1) (var 2) (var 3))

theorem product_query_at (Y Z : Interface) (q p : PTm n) :
    Γ ⊢[PRAAx] ap2 (product Y Z).query q p ≐ queryTerm Y Z q p := by
  have h := toPR_eq (Γ := Γ) (queryTerm Y Z (var 0) (var 1)) ![q, p]
  simpa [product, ap2] using h

theorem product_bound_at (Y Z : Interface) (q p : PTm n) :
    Γ ⊢[PRAAx] ap2 (product Y Z).bound q p ≐ boundTerm Y Z q p := by
  have h := toPR_eq (Γ := Γ) (boundTerm Y Z (var 0) (var 1)) ![q, p]
  simpa [product, ap2] using h

theorem product_verify_at (Y Z : Interface) (c q p : PTm n) :
    Γ ⊢[PRAAx] ap3 (product Y Z).verify c q p ≐ verifyTerm Y Z c q p := by
  have h := toPR_eq (Γ := Γ) (verifyTerm Y Z (var 0) (var 1) (var 2)) ![c, q, p]
  simpa [product, ap3] using h

theorem product_observe_at (Y Z : Interface) (c q p : PTm n) :
    Γ ⊢[PRAAx] ap3 (product Y Z).observe c q p ≐ observeTerm Y Z c q p := by
  have h := toPR_eq (Γ := Γ) (observeTerm Y Z (var 0) (var 1) (var 2)) ![c, q, p]
  simpa [product, ap3] using h

theorem product_relation_at (Y Z : Interface) (o o' q p : PTm n) :
    Γ ⊢[PRAAx] ap4 (product Y Z).related o o' q p ≐ relationTerm Y Z o o' q p := by
  have h := toPR_eq (Γ := Γ) (relationTerm Y Z (var 0) (var 1) (var 2) (var 3)) ![o, o', q, p]
  simpa [product, ap4] using h

/-- The actual product verifier reflects both component validity predicates,
including their decoded exclusive certificate caps. -/
theorem product_verify_sound (Y Z : Interface) (c q p : PTm n)
    (h : Γ ⊢[PRAAx] ap3 (product Y Z).verify c q p ≐ one) :
    Γ ⊢[PRAAx] valid Y (fstT c) (fstT q) p ⋏ valid Z (sndT c) (sndT q) p := by
  have e := eq_of_eqb ((product_verify_at Y Z c q p).eqSymm.eqTrans h)
  have left := (fst_pair _ _).eqSymm.eqTrans ((congrFst e).eqTrans (fst_pair _ _))
  have right := (snd_pair _ _).eqSymm.eqTrans ((congrSnd e).eqTrans (snd_pair _ _))
  exact .andI (validityBit_sound Y _ _ _ left) (validityBit_sound Z _ _ _ right)

theorem product_verify_complete (Y Z : Interface) (c q p : PTm n)
    (hy : Γ ⊢[PRAAx] valid Y (fstT c) (fstT q) p)
    (hz : Γ ⊢[PRAAx] valid Z (sndT c) (sndT q) p) :
    Γ ⊢[PRAAx] ap3 (product Y Z).verify c q p ≐ one :=
  (product_verify_at Y Z c q p).eqTrans
    (eqb_of_eq (pair_congr (validityBit_complete Y _ _ _ hy) (validityBit_complete Z _ _ _ hz)))

theorem product_valid_left (Y Z : Interface) (c q p : PTm n)
    (h : Γ ⊢[PRAAx] valid (product Y Z) c q p) : Γ ⊢[PRAAx] valid Y (fstT c) (fstT q) p :=
  Prf.andE₁ (product_verify_sound Y Z c q p (Prf.andE₂ h))

theorem product_valid_right (Y Z : Interface) (c q p : PTm n)
    (h : Γ ⊢[PRAAx] valid (product Y Z) c q p) : Γ ⊢[PRAAx] valid Z (sndT c) (sndT q) p :=
  Prf.andE₂ (product_verify_sound Y Z c q p (Prf.andE₂ h))

theorem product_intro (Y Z : Interface) (cy cz q p : PTm n)
    (hy : Γ ⊢[PRAAx] valid Y cy (fstT q) p) (hz : Γ ⊢[PRAAx] valid Z cz (sndT q) p) :
    Γ ⊢[PRAAx] valid (product Y Z) (pairT cy cz) q p := by
  have cap := pair_mono (le_of_lt (Prf.andE₁ hy)) (le_of_lt (Prf.andE₁ hz))
  have bounded : Γ ⊢[PRAAx] lt (pairT cy cz) (boundTerm Y Z q p) :=
    (succ_monus_succ _ _).eqTrans cap
  exact .andI (lt_congr (.eqRefl _) (product_bound_at _ _ _ _).eqSymm bounded)
    (product_verify_complete Y Z _ _ _
      (valid_congr Y (fst_pair _ _).eqSymm (.eqRefl _) (.eqRefl _) hy)
      (valid_congr Z (snd_pair _ _).eqSymm (.eqRefl _) (.eqRefl _) hz))

theorem product_observation_fst (Y Z : Interface) (c q p : PTm n) :
    Γ ⊢[PRAAx] fstT (ap3 (product Y Z).observe c q p) ≐ ap3 Y.observe (fstT c) (fstT q) p :=
  (congrFst (product_observe_at _ _ _ _ _)).eqTrans (fst_pair _ _)

theorem product_observation_snd (Y Z : Interface) (c q p : PTm n) :
    Γ ⊢[PRAAx] sndT (ap3 (product Y Z).observe c q p) ≐ ap3 Z.observe (sndT c) (sndT q) p :=
  (congrSnd (product_observe_at _ _ _ _ _)).eqTrans (snd_pair _ _)

theorem product_related_intro (Y Z : Interface) (c c' q p : PTm n)
    (hy : Γ ⊢[PRAAx] related Y (fstT c) (fstT c') (fstT q) p)
    (hz : Γ ⊢[PRAAx] related Z (sndT c) (sndT c') (sndT q) p) :
    Γ ⊢[PRAAx] related (product Y Z) c c' q p := by
  have left : Γ ⊢[PRAAx] ap4 Y.related (fstT (ap3 (product Y Z).observe c q p))
      (fstT (ap3 (product Y Z).observe c' q p)) (fstT q) p ≐ one :=
    (congrApp Y.related (fun i => by
      fin_cases i
      · exact product_observation_fst Y Z c q p
      · exact product_observation_fst Y Z c' q p
      · exact .eqRefl _
      · exact .eqRefl _)).eqTrans hy
  have right : Γ ⊢[PRAAx] ap4 Z.related (sndT (ap3 (product Y Z).observe c q p))
      (sndT (ap3 (product Y Z).observe c' q p)) (sndT q) p ≐ one :=
    (congrApp Z.related (fun i => by
      fin_cases i
      · exact product_observation_snd Y Z c q p
      · exact product_observation_snd Y Z c' q p
      · exact .eqRefl _
      · exact .eqRefl _)).eqTrans hz
  exact (product_relation_at _ _ _ _ _ _).eqTrans (eqb_of_eq (pair_congr left right))

theorem product_related_sound (Y Z : Interface) (c c' q p : PTm n)
    (h : Γ ⊢[PRAAx] related (product Y Z) c c' q p) :
    Γ ⊢[PRAAx] related Y (fstT c) (fstT c') (fstT q) p ⋏ related Z (sndT c) (sndT c') (sndT q) p := by
  have e := eq_of_eqb ((product_relation_at _ _ _ _ _ _).eqSymm.eqTrans h)
  have left := (fst_pair _ _).eqSymm.eqTrans ((congrFst e).eqTrans (fst_pair _ _))
  have right := (snd_pair _ _).eqSymm.eqTrans ((congrSnd e).eqTrans (snd_pair _ _))
  refine .andI ?_ ?_
  · exact (congrApp Y.related (fun i => by
      fin_cases i
      · exact (product_observation_fst Y Z c q p).eqSymm
      · exact (product_observation_fst Y Z c' q p).eqSymm
      · exact .eqRefl _
      · exact .eqRefl _)).eqTrans left
  · exact (congrApp Z.related (fun i => by
      fin_cases i
      · exact (product_observation_snd Y Z c q p).eqSymm
      · exact (product_observation_snd Y Z c' q p).eqSymm
      · exact .eqRefl _
      · exact .eqRefl _)).eqTrans right

#print axioms product_intro
#print axioms product_related_intro

/-! ## Actual append slices supply both bounded submasters -/

theorem left_index_bound (a b i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length a)) :
    Γ ⊢[PRAAx] lt i (length (append a b)) :=
  lt_congr (.eqRefl _) (append_length _ _).eqSymm (lt_of_lt_of_le hi (le_add_right _ _))

theorem right_index_bound (a b i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length b)) :
    Γ ⊢[PRAAx] lt (length a + i) (length (append a b)) :=
  lt_congr (.eqRefl _) (append_length _ _).eqSymm (SequenceComposition.add_lt_left _ hi)

theorem append_master_left_valid (X : Interface) (a b C p : PTm n)
    (hC : Γ ⊢[PRAAx] masterValid X (append a b) C p) :
    Γ ⊢[PRAAx] masterValid X a (slice C zero (length a)) p := by
  apply canonical_master
  refine .allI (.impI ?_)
  have shifted : Γ.map Fm.shift ⊢[PRAAx]
      masterValid X (append (Syn.shift a) (Syn.shift b)) (Syn.shift C) (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hC.shift
  have value := master_values_at X (Prf.andE₂ (Prf.andE₂ shifted.wk))
    (left_index_bound (Syn.shift a) (Syn.shift b) (var 0) Prf.hyp0)
  have certEq : lt (var 0) (length (Syn.shift a)) :: Γ.map Fm.shift ⊢[PRAAx]
      inst2 sliceBody (var 0) (pairT zero (Syn.shift C)) ≐ entry (Syn.shift C) (var 0) :=
    (sliceBody_at _ _ _).eqTrans (entry_congr (.eqRefl _) (zero_add _))
  have queryEq := append_left (b := Syn.shift b)
    (Prf.hyp0 : lt (var 0) (length (Syn.shift a)) :: Γ.map Fm.shift ⊢[PRAAx] _)
  simpa only [Syn.shift, subst_pairT, ConciseIPRA.PTm.subst_zero] using
    valid_congr X certEq.eqSymm queryEq (.eqRefl _) value

theorem append_master_right_valid (X : Interface) (a b C p : PTm n)
    (hC : Γ ⊢[PRAAx] masterValid X (append a b) C p) :
    Γ ⊢[PRAAx] masterValid X b (slice C (length a) (length b)) p := by
  apply canonical_master
  refine .allI (.impI ?_)
  have shifted : Γ.map Fm.shift ⊢[PRAAx]
      masterValid X (append (Syn.shift a) (Syn.shift b)) (Syn.shift C) (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hC.shift
  have value := master_values_at X (Prf.andE₂ (Prf.andE₂ shifted.wk))
    (right_index_bound (Syn.shift a) (Syn.shift b) (var 0) Prf.hyp0)
  have certEq := sliceBody_at (Γ := lt (var 0) (length (Syn.shift b)) :: Γ.map Fm.shift)
    (Syn.shift C) (length (Syn.shift a)) (var 0)
  have queryEq := append_right (a := Syn.shift a)
    (Prf.hyp0 : lt (var 0) (length (Syn.shift b)) :: Γ.map Fm.shift ⊢[PRAAx] _)
  simpa only [Syn.shift, subst_pairT, SequenceComposition.subst_length] using
    valid_congr X certEq.eqSymm queryEq (.eqRefl _) value

theorem append_master_left_related (X : Interface) (a b C C' p : PTm n)
    (hrel : Γ ⊢[PRAAx] masterRelated X (append a b) C C' p) :
    Γ ⊢[PRAAx] masterRelated X a (slice C zero (length a)) (slice C' zero (length a)) p := by
  refine .allI (.impI ?_)
  have shifted : Γ.map Fm.shift ⊢[PRAAx] masterRelated X (append (Syn.shift a) (Syn.shift b))
      (Syn.shift C) (Syn.shift C') (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hrel.shift
  have value := master_related_at X shifted.wk
    (left_index_bound (Syn.shift a) (Syn.shift b) (var 0) Prf.hyp0)
  have certEq : lt (var 0) (length (Syn.shift a)) :: Γ.map Fm.shift ⊢[PRAAx]
      entry (slice (Syn.shift C) zero (length (Syn.shift a))) (var 0) ≐ entry (Syn.shift C) (var 0) :=
    (slice_lookup _ _ _ _ Prf.hyp0).eqTrans (entry_congr (.eqRefl _) (zero_add _))
  have certEq' : lt (var 0) (length (Syn.shift a)) :: Γ.map Fm.shift ⊢[PRAAx]
      entry (slice (Syn.shift C') zero (length (Syn.shift a))) (var 0) ≐ entry (Syn.shift C') (var 0) :=
    (slice_lookup _ _ _ _ Prf.hyp0).eqTrans (entry_congr (.eqRefl _) (zero_add _))
  have queryEq := append_left (b := Syn.shift b)
    (Prf.hyp0 : lt (var 0) (length (Syn.shift a)) :: Γ.map Fm.shift ⊢[PRAAx] _)
  simpa only [Syn.shift, subst_slice, ConciseIPRA.PTm.subst_zero, SequenceComposition.subst_length] using
    related_congr X certEq.eqSymm certEq'.eqSymm queryEq (.eqRefl _) value

theorem append_master_right_related (X : Interface) (a b C C' p : PTm n)
    (hrel : Γ ⊢[PRAAx] masterRelated X (append a b) C C' p) :
    Γ ⊢[PRAAx] masterRelated X b (slice C (length a) (length b)) (slice C' (length a) (length b)) p := by
  refine .allI (.impI ?_)
  have shifted : Γ.map Fm.shift ⊢[PRAAx] masterRelated X (append (Syn.shift a) (Syn.shift b))
      (Syn.shift C) (Syn.shift C') (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hrel.shift
  have value := master_related_at X shifted.wk
    (right_index_bound (Syn.shift a) (Syn.shift b) (var 0) Prf.hyp0)
  have certEq := slice_lookup (Γ := lt (var 0) (length (Syn.shift b)) :: Γ.map Fm.shift)
    (Syn.shift C) (length (Syn.shift a)) (length (Syn.shift b)) (var 0) Prf.hyp0
  have certEq' := slice_lookup (Γ := lt (var 0) (length (Syn.shift b)) :: Γ.map Fm.shift)
    (Syn.shift C') (length (Syn.shift a)) (length (Syn.shift b)) (var 0) Prf.hyp0
  have queryEq := append_right (a := Syn.shift a)
    (Prf.hyp0 : lt (var 0) (length (Syn.shift b)) :: Γ.map Fm.shift ⊢[PRAAx] _)
  simpa only [Syn.shift, subst_slice, SequenceComposition.subst_length] using
    related_congr X certEq.eqSymm certEq'.eqSymm queryEq (.eqRefl _) value

/-! ## Actual fanout programs and query-specialized obligations -/

def demandTerm {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) (q p : PTm n) : PTm n :=
  append (ap2 R.demand (fstT q) p) (ap2 S.demand (sndT q) p)

def demandF {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) : PR 2 :=
  PTm.toPR (demandTerm R S (var 0) (var 1))

def leftMaster {X Y Z : Interface} (R : Realizer X Y) (_S : Realizer X Z) (C q p : PTm n) : PTm n :=
  slice C zero (length (ap2 R.demand (fstT q) p))

def rightMaster {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) (C q p : PTm n) : PTm n :=
  slice C (length (ap2 R.demand (fstT q) p)) (length (ap2 S.demand (sndT q) p))

def transformTerm {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) (C q p : PTm n) : PTm n :=
  pairT (ap3 R.transform (leftMaster R S C q p) (fstT q) p)
    (ap3 S.transform (rightMaster R S C q p) (sndT q) p)

def transformF {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) : PR 3 :=
  PTm.toPR (transformTerm R S (var 0) (var 1) (var 2))

ipra_subst demandTerm
ipra_subst leftMaster
ipra_subst rightMaster
ipra_subst transformTerm

theorem demand_at {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) (q p : PTm n) :
    Γ ⊢[PRAAx] ap2 (demandF R S) q p ≐ demandTerm R S q p := by
  have h := toPR_eq (Γ := Γ) (demandTerm R S (var 0) (var 1)) ![q, p]
  simpa [demandF, ap2] using h

theorem transform_at {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) (C q p : PTm n) :
    Γ ⊢[PRAAx] ap3 (transformF R S) C q p ≐ transformTerm R S C q p := by
  have h := toPR_eq (Γ := Γ) (transformTerm R S (var 0) (var 1) (var 2)) ![C, q, p]
  simpa [transformF, ap3] using h

def leftTemplate (A : Fm PTm 2) : Fm PTm 2 := queryAt A (fstT (var 0)) (var 1)
def rightTemplate (A : Fm PTm 2) : Fm PTm 2 := queryAt A (sndT (var 0)) (var 1)

theorem leftTemplate_at (A : Fm PTm 2) (q p : PTm n) :
    (leftTemplate A).subst ![q, p] = queryAt A (fstT q) p := by
  simp only [leftTemplate, subst_queryAt, subst_fstT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one]

theorem rightTemplate_at (A : Fm PTm 2) (q p : PTm n) :
    (rightTemplate A).subst ![q, p] = queryAt A (sndT q) p := by
  simp only [rightTemplate, subst_queryAt, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one]

def fanoutGuard {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) : Fm PTm 2 :=
  leftTemplate R.guard ⋏ rightTemplate S.guard

def fanoutResiduals {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) : List (Fm PTm 2) :=
  R.residuals.map leftTemplate ++ S.residuals.map rightTemplate

theorem guard_parts {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) (q p : PTm n)
    (h : Γ ⊢[PRAAx] queryAt (fanoutGuard R S) q p) :
    Γ ⊢[PRAAx] queryAt R.guard (fstT q) p ⋏ queryAt S.guard (sndT q) p := by
  simpa only [queryAt, fanoutGuard, Fm.subst_and, leftTemplate_at, rightTemplate_at] using h

theorem residuals_left {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) (q p : PTm n)
    (h : Γ ⊢[PRAAx] queryAt (allOf (fanoutResiduals R S)) q p) :
    Γ ⊢[PRAAx] queryAt (allOf R.residuals) (fstT q) p := by
  apply allOf_at_intro R.residuals ![fstT q, p]
  intro A hA
  have member : leftTemplate A ∈ fanoutResiduals R S := List.mem_append_left _ (List.mem_map.mpr ⟨A, hA, rfl⟩)
  have selected := allOf_at_elim (fanoutResiduals R S) ![q, p] h member
  rw [leftTemplate_at] at selected
  exact selected

theorem residuals_right {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) (q p : PTm n)
    (h : Γ ⊢[PRAAx] queryAt (allOf (fanoutResiduals R S)) q p) :
    Γ ⊢[PRAAx] queryAt (allOf S.residuals) (sndT q) p := by
  apply allOf_at_intro S.residuals ![sndT q, p]
  intro A hA
  have member : rightTemplate A ∈ fanoutResiduals R S := List.mem_append_right _ (List.mem_map.mpr ⟨A, hA, rfl⟩)
  have selected := allOf_at_elim (fanoutResiduals R S) ![q, p] h member
  rw [rightTemplate_at] at selected
  exact selected

#print axioms append_master_left_valid
#print axioms append_master_right_valid

theorem fanout_sound {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) (C q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt (fanoutGuard R S) q p)
    (hr : Γ ⊢[PRAAx] queryAt (allOf (fanoutResiduals R S)) q p)
    (hC : Γ ⊢[PRAAx] masterValid X (ap2 (demandF R S) q p) C p) :
    Γ ⊢[PRAAx] valid (product Y Z) (ap3 (transformF R S) C q p) q p := by
  have guards := guard_parts R S q p hg
  have source := masterValid_congr X (demand_at R S q p) (.eqRefl _) (.eqRefl _) hC
  have left := R.applySound (leftMaster R S C q p) (fstT q) p
    (Prf.andE₁ guards) (residuals_left R S q p hr) (append_master_left_valid X _ _ _ _ source)
  have right := S.applySound (rightMaster R S C q p) (sndT q) p
    (Prf.andE₂ guards) (residuals_right R S q p hr) (append_master_right_valid X _ _ _ _ source)
  have paired := product_intro Y Z _ _ q p left right
  exact valid_congr (product Y Z) (transform_at R S C q p).eqSymm (.eqRefl _) (.eqRefl _) paired

theorem fanout_stable {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) (C C' q p : PTm n)
    (hg : Γ ⊢[PRAAx] queryAt (fanoutGuard R S) q p)
    (hr : Γ ⊢[PRAAx] queryAt (allOf (fanoutResiduals R S)) q p)
    (hC : Γ ⊢[PRAAx] masterValid X (ap2 (demandF R S) q p) C p)
    (hC' : Γ ⊢[PRAAx] masterValid X (ap2 (demandF R S) q p) C' p)
    (hrel : Γ ⊢[PRAAx] masterRelated X (ap2 (demandF R S) q p) C C' p) :
    Γ ⊢[PRAAx] related (product Y Z) (ap3 (transformF R S) C q p) (ap3 (transformF R S) C' q p) q p := by
  have guards := guard_parts R S q p hg
  have source := masterValid_congr X (demand_at R S q p) (.eqRefl _) (.eqRefl _) hC
  have source' := masterValid_congr X (demand_at R S q p) (.eqRefl _) (.eqRefl _) hC'
  have relation := masterRelated_congr X (demand_at R S q p) (.eqRefl _) (.eqRefl _) (.eqRefl _) hrel
  have left := R.applyStable (leftMaster R S C q p) (leftMaster R S C' q p) (fstT q) p
    (Prf.andE₁ guards) (residuals_left R S q p hr)
    (append_master_left_valid X _ _ _ _ source) (append_master_left_valid X _ _ _ _ source')
    (append_master_left_related X _ _ _ _ _ relation)
  have right := S.applyStable (rightMaster R S C q p) (rightMaster R S C' q p) (sndT q) p
    (Prf.andE₂ guards) (residuals_right R S q p hr)
    (append_master_right_valid X _ _ _ _ source) (append_master_right_valid X _ _ _ _ source')
    (append_master_right_related X _ _ _ _ _ relation)
  have pairLeft : Γ ⊢[PRAAx] related Y (fstT (transformTerm R S C q p))
      (fstT (transformTerm R S C' q p)) (fstT q) p :=
    related_congr Y (fst_pair _ _).eqSymm (fst_pair _ _).eqSymm (.eqRefl _) (.eqRefl _) left
  have pairRight : Γ ⊢[PRAAx] related Z (sndT (transformTerm R S C q p))
      (sndT (transformTerm R S C' q p)) (sndT q) p :=
    related_congr Z (snd_pair _ _).eqSymm (snd_pair _ _).eqSymm (.eqRefl _) (.eqRefl _) right
  have paired := product_related_intro Y Z _ _ q p pairLeft pairRight
  exact related_congr (product Y Z) (transform_at R S C q p).eqSymm (transform_at R S C' q p).eqSymm
    (.eqRefl _) (.eqRefl _) paired

/-- Genuine fanout: both child demand lists are consumed, both canonical
submasters are verified, both child transformers run, and their outputs pair. -/
def fanout {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) : Realizer X (product Y Z) where
  demand := demandF R S
  transform := transformF R S
  guard := fanoutGuard R S
  residuals := fanoutResiduals R S
  sound := by
    let Δ : List (Fm PTm 3) := [(fanoutGuard R S).shift, (allOf (fanoutResiduals R S)).shift,
      masterValid X (ap2 (demandF R S) (var 1) (var 2)) (var 0) (var 2)]
    have hg : Δ ⊢[PRAAx] queryAt (fanoutGuard R S) (var 1) (var 2) := by rw [queryAt_shift3]; exact Prf.hyp0
    have hr : Δ ⊢[PRAAx] queryAt (allOf (fanoutResiduals R S)) (var 1) (var 2) := by rw [queryAt_shift3]; exact Prf.hyp1
    exact fanout_sound R S (var 0) (var 1) (var 2) hg hr hyp2
  stable := by
    let Δ : List (Fm PTm 4) := [(fanoutGuard R S).shift.shift, (allOf (fanoutResiduals R S)).shift.shift,
      masterValid X (ap2 (demandF R S) (var 2) (var 3)) (var 0) (var 3),
      masterValid X (ap2 (demandF R S) (var 2) (var 3)) (var 1) (var 3),
      masterRelated X (ap2 (demandF R S) (var 2) (var 3)) (var 0) (var 1) (var 3)]
    have hg : Δ ⊢[PRAAx] queryAt (fanoutGuard R S) (var 2) (var 3) := by rw [queryAt_shift4]; exact Prf.hyp0
    have hr : Δ ⊢[PRAAx] queryAt (allOf (fanoutResiduals R S)) (var 2) (var 3) := by rw [queryAt_shift4]; exact Prf.hyp1
    exact fanout_stable R S (var 0) (var 1) (var 2) (var 3) hg hr hyp2 hyp2.wk hyp2.wk.wk

#print axioms fanout
#print axioms fanout_stable

/-! ## Projection realizers with actual one-query product demands -/

def singleton (q : PTm n) : PTm n := sequence (var 1) one q

ipra_subst singleton

theorem singleton_length (q : PTm n) : Γ ⊢[PRAAx] length (singleton q) ≐ one :=
  MasterCertificate.sequence_length _ _ _

theorem singleton_entry (q : PTm n) : Γ ⊢[PRAAx] entry (singleton q) zero ≐ q := by
  have h := sequence_decode (var 1 : PTm 2) (x := q) (i := zero) (le_refl (Γ := Γ) one)
  simpa [singleton, inst2] using h

theorem singleton_master_value (X : Interface) (q C p : PTm n)
    (h : Γ ⊢[PRAAx] masterValid X (singleton q) C p) :
    Γ ⊢[PRAAx] valid X (entry C zero) q p := by
  have hi : Γ ⊢[PRAAx] lt zero (length (singleton q)) :=
    lt_congr (.eqRefl _) (singleton_length q).eqSymm (le_refl one)
  exact valid_congr X (.eqRefl _) (singleton_entry q) (.eqRefl _)
    (master_values_at X (Prf.andE₂ (Prf.andE₂ h)) hi)

theorem singleton_master_related (X : Interface) (q C C' p : PTm n)
    (h : Γ ⊢[PRAAx] masterRelated X (singleton q) C C' p) :
    Γ ⊢[PRAAx] related X (entry C zero) (entry C' zero) q p := by
  have hi : Γ ⊢[PRAAx] lt zero (length (singleton q)) :=
    lt_congr (.eqRefl _) (singleton_length q).eqSymm (le_refl one)
  exact related_congr X (.eqRefl _) (.eqRefl _) (singleton_entry q) (.eqRefl _) (master_related_at X h hi)

def leftDemandTerm (companion : PR 2) (q p : PTm n) : PTm n := singleton (pairT q (ap2 companion q p))
def rightDemandTerm (companion : PR 2) (q p : PTm n) : PTm n := singleton (pairT (ap2 companion q p) q)
def leftDemandF (companion : PR 2) : PR 2 := PTm.toPR (leftDemandTerm companion (var 0) (var 1))
def rightDemandF (companion : PR 2) : PR 2 := PTm.toPR (rightDemandTerm companion (var 0) (var 1))
def leftTransformF : PR 3 := PTm.toPR (fstT (entry (var 0) zero))
def rightTransformF : PR 3 := PTm.toPR (sndT (entry (var 0) zero))

ipra_subst leftDemandTerm
ipra_subst rightDemandTerm

theorem leftDemand_at (companion : PR 2) (q p : PTm n) :
    Γ ⊢[PRAAx] ap2 (leftDemandF companion) q p ≐ leftDemandTerm companion q p := by
  have h := toPR_eq (Γ := Γ) (leftDemandTerm companion (var 0) (var 1)) ![q, p]
  simpa [leftDemandF, ap2] using h

theorem rightDemand_at (companion : PR 2) (q p : PTm n) :
    Γ ⊢[PRAAx] ap2 (rightDemandF companion) q p ≐ rightDemandTerm companion q p := by
  have h := toPR_eq (Γ := Γ) (rightDemandTerm companion (var 0) (var 1)) ![q, p]
  simpa [rightDemandF, ap2] using h

theorem leftTransform_at (C q p : PTm n) :
    Γ ⊢[PRAAx] ap3 leftTransformF C q p ≐ fstT (entry C zero) := by
  have h := toPR_eq (Γ := Γ) (fstT (entry (var 0 : PTm 3) zero)) ![C, q, p]
  simpa [leftTransformF, ap3] using h

theorem rightTransform_at (C q p : PTm n) :
    Γ ⊢[PRAAx] ap3 rightTransformF C q p ≐ sndT (entry C zero) := by
  have h := toPR_eq (Γ := Γ) (sndT (entry (var 0 : PTm 3) zero)) ![C, q, p]
  simpa [rightTransformF, ap3] using h

theorem projection_left_sound (Y Z : Interface) (companion : PR 2) (C q p : PTm n)
    (hC : Γ ⊢[PRAAx] masterValid (product Y Z) (ap2 (leftDemandF companion) q p) C p) :
    Γ ⊢[PRAAx] valid Y (ap3 leftTransformF C q p) q p := by
  have source := masterValid_congr (product Y Z) (leftDemand_at companion q p) (.eqRefl _) (.eqRefl _) hC
  have pairValid := singleton_master_value (product Y Z) (pairT q (ap2 companion q p)) C p source
  have projected := product_valid_left Y Z _ _ p pairValid
  exact valid_congr Y (leftTransform_at C q p).eqSymm (fst_pair _ _) (.eqRefl _) projected

theorem projection_right_sound (Y Z : Interface) (companion : PR 2) (C q p : PTm n)
    (hC : Γ ⊢[PRAAx] masterValid (product Y Z) (ap2 (rightDemandF companion) q p) C p) :
    Γ ⊢[PRAAx] valid Z (ap3 rightTransformF C q p) q p := by
  have source := masterValid_congr (product Y Z) (rightDemand_at companion q p) (.eqRefl _) (.eqRefl _) hC
  have pairValid := singleton_master_value (product Y Z) (pairT (ap2 companion q p) q) C p source
  have projected := product_valid_right Y Z _ _ p pairValid
  exact valid_congr Z (rightTransform_at C q p).eqSymm (snd_pair _ _) (.eqRefl _) projected

theorem projection_left_stable (Y Z : Interface) (companion : PR 2) (C C' q p : PTm n)
    (hrel : Γ ⊢[PRAAx] masterRelated (product Y Z) (ap2 (leftDemandF companion) q p) C C' p) :
    Γ ⊢[PRAAx] related Y (ap3 leftTransformF C q p) (ap3 leftTransformF C' q p) q p := by
  have source := masterRelated_congr (product Y Z) (leftDemand_at companion q p)
    (.eqRefl _) (.eqRefl _) (.eqRefl _) hrel
  have pairRelated := singleton_master_related (product Y Z) (pairT q (ap2 companion q p)) C C' p source
  have projected := Prf.andE₁ (product_related_sound Y Z _ _ _ p pairRelated)
  exact related_congr Y (leftTransform_at C q p).eqSymm (leftTransform_at C' q p).eqSymm
    (fst_pair _ _) (.eqRefl _) projected

theorem projection_right_stable (Y Z : Interface) (companion : PR 2) (C C' q p : PTm n)
    (hrel : Γ ⊢[PRAAx] masterRelated (product Y Z) (ap2 (rightDemandF companion) q p) C C' p) :
    Γ ⊢[PRAAx] related Z (ap3 rightTransformF C q p) (ap3 rightTransformF C' q p) q p := by
  have source := masterRelated_congr (product Y Z) (rightDemand_at companion q p)
    (.eqRefl _) (.eqRefl _) (.eqRefl _) hrel
  have pairRelated := singleton_master_related (product Y Z) (pairT (ap2 companion q p) q) C C' p source
  have projected := Prf.andE₂ (product_related_sound Y Z _ _ _ p pairRelated)
  exact related_congr Z (rightTransform_at C q p).eqSymm (rightTransform_at C' q p).eqSymm
    (snd_pair _ _) (.eqRefl _) projected

/-- The companion is an explicit fixed PR query selector for the component
not exported by this projection. No certificate is invented for that query. -/
def projectLeft (Y Z : Interface) (companion : PR 2) : Realizer (product Y Z) Y where
  demand := leftDemandF companion
  transform := leftTransformF
  guard := (zero ≐ zero : Fm PTm 2)
  residuals := []
  sound := projection_left_sound Y Z companion _ _ _ hyp2
  stable := projection_left_stable Y Z companion _ _ _ _ hyp2.wk.wk

def projectRight (Y Z : Interface) (companion : PR 2) : Realizer (product Y Z) Z where
  demand := rightDemandF companion
  transform := rightTransformF
  guard := (zero ≐ zero : Fm PTm 2)
  residuals := []
  sound := projection_right_sound Y Z companion _ _ _ hyp2
  stable := projection_right_stable Y Z companion _ _ _ _ hyp2.wk.wk

#print axioms projectLeft
#print axioms projectRight

/-! ## Closed pair-node contracts and literal residual sequents -/

theorem product_query_sound (Y Z : Interface) (q p : PTm n)
    (h : Γ ⊢[PRAAx] ap2 (product Y Z).query q p ≐ one) :
    Γ ⊢[PRAAx] (ap2 Y.query (fstT q) p ≐ one) ⋏ (ap2 Z.query (sndT q) p ≐ one) := by
  have e := eq_of_eqb ((product_query_at Y Z q p).eqSymm.eqTrans h)
  exact .andI ((fst_pair _ _).eqSymm.eqTrans ((congrFst e).eqTrans (fst_pair _ _)))
    ((snd_pair _ _).eqSymm.eqTrans ((congrSnd e).eqTrans (snd_pair _ _)))

theorem product_query_complete (Y Z : Interface) (q p : PTm n)
    (hy : Γ ⊢[PRAAx] ap2 Y.query (fstT q) p ≐ one)
    (hz : Γ ⊢[PRAAx] ap2 Z.query (sndT q) p ≐ one) :
    Γ ⊢[PRAAx] ap2 (product Y Z).query q p ≐ one :=
  (product_query_at Y Z q p).eqTrans (eqb_of_eq (pair_congr hy hz))

def productQueryFormula (Y Z : Interface) : Fm PTm 2 :=
  ((ap2 (product Y Z).query (var 0) (var 1) ≐ one) ⟶
    ((ap2 Y.query (fstT (var 0)) (var 1) ≐ one) ⋏ (ap2 Z.query (sndT (var 0)) (var 1) ≐ one))) ⋏
  (((ap2 Y.query (fstT (var 0)) (var 1) ≐ one) ⋏ (ap2 Z.query (sndT (var 0)) (var 1) ≐ one)) ⟶
    (ap2 (product Y Z).query (var 0) (var 1) ≐ one))

theorem bounded_product_query (Y Z : Interface) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (productQueryFormula Y Z) :=
  closeUniv 2 (.andI (.impI (product_query_sound Y Z _ _ Prf.hyp0))
    (.impI (product_query_complete Y Z _ _ (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0))))

def productProgramsFormula (Y Z : Interface) : Fm PTm 4 :=
  (ap2 (product Y Z).query (var 2) (var 3) ≐ queryTerm Y Z (var 2) (var 3)) ⋏
  ((ap2 (product Y Z).bound (var 2) (var 3) ≐ boundTerm Y Z (var 2) (var 3)) ⋏
  ((ap3 (product Y Z).verify (var 0) (var 2) (var 3) ≐ verifyTerm Y Z (var 0) (var 2) (var 3)) ⋏
  ((ap3 (product Y Z).observe (var 0) (var 2) (var 3) ≐ observeTerm Y Z (var 0) (var 2) (var 3)) ⋏
    (ap4 (product Y Z).related (var 0) (var 1) (var 2) (var 3) ≐
      relationTerm Y Z (var 0) (var 1) (var 2) (var 3)))))

theorem product_program_metadata (Y Z : Interface) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (productProgramsFormula Y Z) :=
  closeUniv 4 (.andI (product_query_at Y Z _ _) (.andI (product_bound_at Y Z _ _)
    (.andI (product_verify_at Y Z _ _ _) (.andI (product_observe_at Y Z _ _ _)
      (product_relation_at Y Z _ _ _ _)))))

theorem product_verify_cases (Y Z : Interface) (c q p : PTm n) :
    Γ ⊢[PRAAx] (ap3 (product Y Z).verify c q p ≐ zero) ⋎
      (ap3 (product Y Z).verify c q p ≐ one) := by
  refine .orE (eqb_cases
    (pairT (validityBit Y (fstT c) (fstT q) p) (validityBit Z (sndT c) (sndT q) p))
    (pairT one one)) ?_ ?_
  · exact .orI₁ ((product_verify_at Y Z c q p).eqTrans Prf.hyp0)
  · exact .orI₂ ((product_verify_at Y Z c q p).eqTrans Prf.hyp0)

/-- The verifier itself reflects both decoded bounded component contracts.
For an arbitrary, possibly noncanonical code, the separate product cap is
still part of `valid`; no unproved surjectivity of `pairT` is used. -/
def productVerifierFormula (Y Z : Interface) : Fm PTm 3 :=
  ((ap3 (product Y Z).verify (var 0) (var 1) (var 2) ≐ zero) ⋎
    (ap3 (product Y Z).verify (var 0) (var 1) (var 2) ≐ one)) ⋏
  (((ap3 (product Y Z).verify (var 0) (var 1) (var 2) ≐ one) ⟶
    (valid Y (fstT (var 0)) (fstT (var 1)) (var 2) ⋏
      valid Z (sndT (var 0)) (sndT (var 1)) (var 2))) ⋏
  ((valid Y (fstT (var 0)) (fstT (var 1)) (var 2) ⋏
    valid Z (sndT (var 0)) (sndT (var 1)) (var 2)) ⟶
      (ap3 (product Y Z).verify (var 0) (var 1) (var 2) ≐ one)))

theorem bounded_product_verifier (Y Z : Interface) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (productVerifierFormula Y Z) :=
  closeUniv 3 (.andI (product_verify_cases Y Z _ _ _) (.andI
    (.impI (product_verify_sound Y Z _ _ _ Prf.hyp0))
    (.impI (product_verify_complete Y Z _ _ _ (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0)))))

def productIntroFormula (Y Z : Interface) : Fm PTm 4 :=
  valid Y (var 0) (fstT (var 2)) (var 3) ⟶
    valid Z (var 1) (sndT (var 2)) (var 3) ⟶
      valid (product Y Z) (pairT (var 0) (var 1)) (var 2) (var 3)

theorem bounded_product_intro (Y Z : Interface) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (productIntroFormula Y Z) :=
  closeUniv 4 (.impI (.impI (product_intro Y Z _ _ _ _ Prf.hyp1 Prf.hyp0)))

def productRelationFormula (Y Z : Interface) : Fm PTm 4 :=
  (related (product Y Z) (var 0) (var 1) (var 2) (var 3) ⟶
    (related Y (fstT (var 0)) (fstT (var 1)) (fstT (var 2)) (var 3) ⋏
      related Z (sndT (var 0)) (sndT (var 1)) (sndT (var 2)) (var 3))) ⋏
  ((related Y (fstT (var 0)) (fstT (var 1)) (fstT (var 2)) (var 3) ⋏
    related Z (sndT (var 0)) (sndT (var 1)) (sndT (var 2)) (var 3)) ⟶
      related (product Y Z) (var 0) (var 1) (var 2) (var 3))

theorem bounded_product_relation (Y Z : Interface) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (productRelationFormula Y Z) :=
  closeUniv 4 (.andI (.impI (product_related_sound Y Z _ _ _ _ Prf.hyp0))
    (.impI (product_related_intro Y Z _ _ _ _ (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0))))

/-- Optional component certificate-independence laws give a product law;
they are not premises of the fanout constructor or its stability theorem. -/
theorem productObservationInvariant {Y Z : Interface}
    (hy : ObservationInvariant Y) (hz : ObservationInvariant Z) : ObservationInvariant (product Y Z) where
  proof := product_related_intro Y Z _ _ _ _
    (hy.apply _ _ _ _ (product_valid_left Y Z _ _ _ Prf.hyp0) (product_valid_left Y Z _ _ _ Prf.hyp1))
    (hz.apply _ _ _ _ (product_valid_right Y Z _ _ _ Prf.hyp0) (product_valid_right Y Z _ _ _ Prf.hyp1))

/-- Actual demand append, paired transformer and generated bounded metadata.
Variables are `0=C`, `1=q`, `2=p`. -/
def fanoutProgramsFormula {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) : Fm PTm 3 :=
  (ap2 (fanout R S).demand (var 1) (var 2) ≐
    append (ap2 R.demand (fstT (var 1)) (var 2)) (ap2 S.demand (sndT (var 1)) (var 2))) ⋏
  ((ap3 (fanout R S).transform (var 0) (var 1) (var 2) ≐
    pairT (ap3 R.transform (leftMaster R S (var 0) (var 1) (var 2)) (fstT (var 1)) (var 2))
      (ap3 S.transform (rightMaster R S (var 0) (var 1) (var 2)) (sndT (var 1)) (var 2))) ⋏
    metadataFormula (fanout R S))

theorem fiber_fanout_programs {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (fanoutProgramsFormula R S) :=
  closeUniv 3 (.andI (demand_at R S _ _) (.andI (transform_at R S _ _ _)
    (.andI ((fanout R S).inputBound_at _ _) (.andI ((fanout R S).inputVerifier_at _ _ _)
      ((fanout R S).outputObservation_at _ _ _)))))

theorem bounded_fanout_verifier {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (verifierFormula (fanout R S)) :=
  bounded_master_verifier (fanout R S)

theorem fiber_realizer_fanout {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (soundFormula (fanout R S)) :=
  bounded_realizer_soundness (fanout R S)

theorem fiber_realizer_fanout_stable {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (stabilityFormula (fanout R S)) :=
  bounded_realizer_stability (fanout R S)

theorem fiber_realizer_fanout_sealed {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (sealedFormula (fanout R S)) :=
  bounded_realizer_sealed (fanout R S)

/-- Each original residual is specialized at its own decoded output query,
with the same persistent input parameter. -/
def fanoutResidualContext {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z)
    (q p : PTm n) : List (Fm PTm n) := (fanoutResiduals R S).map (fun A => queryAt A q p)

theorem fiber_fanout_sequent {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) (C q p : PTm n) :
    (fanoutResidualContext R S q p ++ [queryAt (fanoutGuard R S) q p,
      ap3 (fanout R S).inputVerifierF C q p ≐ one]) ⊢[PRAAx]
        valid (product Y Z) (ap3 (fanout R S).transform C q p) q p := by
  apply (fanout R S).applySound C q p
  · exact .hyp (List.mem_append_right _ (List.mem_cons_self))
  · apply allOf_at_intro (fanoutResiduals R S) ![q, p]
    intro A hA
    exact .hyp (List.mem_append_left _ (List.mem_map.mpr ⟨A, hA, rfl⟩))
  · apply (fanout R S).verifier_sound C q p
    exact .hyp (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

theorem fiber_fanout_sealed_sequent {X Y Z : Interface} (R : Realizer X Y) (S : Realizer X Z) (q p : PTm n) :
    (fanoutResidualContext R S q p ++ [queryAt (fanoutGuard R S) q p, inputTotal (fanout R S) q p]) ⊢[PRAAx]
      outputTotal (product Y Z) q p := by
  apply (fanout R S).seal q p
  · exact .hyp (List.mem_append_right _ (List.mem_cons_self))
  · apply allOf_at_intro (fanoutResiduals R S) ![q, p]
    intro A hA
    exact .hyp (List.mem_append_left _ (List.mem_map.mpr ⟨A, hA, rfl⟩))
  · exact .hyp (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

/-- Projection has no residual or guard obligation. The input verifier
still checks the actual one-element product master and both decoded caps. -/
def projectionSoundFormula (Y Z : Interface) (companion : PR 2) : Fm PTm 3 :=
  ((ap3 (projectLeft Y Z companion).inputVerifierF (var 0) (var 1) (var 2) ≐ one) ⟶
    valid Y (ap3 leftTransformF (var 0) (var 1) (var 2)) (var 1) (var 2)) ⋏
  ((ap3 (projectRight Y Z companion).inputVerifierF (var 0) (var 1) (var 2) ≐ one) ⟶
    valid Z (ap3 rightTransformF (var 0) (var 1) (var 2)) (var 1) (var 2))

theorem bounded_projections (Y Z : Interface) (companion : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3 (projectionSoundFormula Y Z companion) :=
  closeUniv 3 (.andI
    (.impI (projection_left_sound Y Z companion _ _ _ ((projectLeft Y Z companion).verifier_sound _ _ _ Prf.hyp0)))
    (.impI (projection_right_sound Y Z companion _ _ _ ((projectRight Y Z companion).verifier_sound _ _ _ Prf.hyp0))))

def projectionStabilityFormula (Y Z : Interface) (companion : PR 2) : Fm PTm 4 :=
  (masterRelated (product Y Z) (ap2 (leftDemandF companion) (var 2) (var 3)) (var 0) (var 1) (var 3) ⟶
    related Y (ap3 leftTransformF (var 0) (var 2) (var 3))
      (ap3 leftTransformF (var 1) (var 2) (var 3)) (var 2) (var 3)) ⋏
  (masterRelated (product Y Z) (ap2 (rightDemandF companion) (var 2) (var 3)) (var 0) (var 1) (var 3) ⟶
    related Z (ap3 rightTransformF (var 0) (var 2) (var 3))
      (ap3 rightTransformF (var 1) (var 2) (var 3)) (var 2) (var 3))

theorem bounded_projections_stable (Y Z : Interface) (companion : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (projectionStabilityFormula Y Z companion) :=
  closeUniv 4 (.andI (.impI (projection_left_stable Y Z companion _ _ _ _ Prf.hyp0))
    (.impI (projection_right_stable Y Z companion _ _ _ _ Prf.hyp0)))

def projectionSealedFormula (Y Z : Interface) (companion : PR 2) : Fm PTm 2 :=
  (inputTotal (projectLeft Y Z companion) (var 0) (var 1) ⟶ outputTotal Y (var 0) (var 1)) ⋏
  (inputTotal (projectRight Y Z companion) (var 0) (var 1) ⟶ outputTotal Z (var 0) (var 1))

theorem bounded_projections_sealed (Y Z : Interface) (companion : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 (projectionSealedFormula Y Z companion) :=
  closeUniv 2 (.andI
    (.impI ((projectLeft Y Z companion).seal _ _
      (by simp only [projectLeft, queryAt, Fm.subst_eq, ConciseIPRA.PTm.subst_zero]; exact .eqRefl zero)
      (by simp only [projectLeft, allOf, queryAt, Fm.subst_eq, ConciseIPRA.PTm.subst_zero]; exact .eqRefl zero)
      Prf.hyp0))
    (.impI ((projectRight Y Z companion).seal _ _
      (by simp only [projectRight, queryAt, Fm.subst_eq, ConciseIPRA.PTm.subst_zero]; exact .eqRefl zero)
      (by simp only [projectRight, allOf, queryAt, Fm.subst_eq, ConciseIPRA.PTm.subst_zero]; exact .eqRefl zero)
      Prf.hyp0)))

#print axioms bounded_product_verifier
#print axioms bounded_product_query
#print axioms product_program_metadata
#print axioms bounded_product_intro
#print axioms bounded_product_relation
#print axioms productObservationInvariant
#print axioms fiber_fanout_programs
#print axioms bounded_fanout_verifier
#print axioms fiber_realizer_fanout
#print axioms fiber_realizer_fanout_stable
#print axioms fiber_realizer_fanout_sealed
#print axioms fiber_fanout_sequent
#print axioms fiber_fanout_sealed_sequent
#print axioms bounded_projections
#print axioms bounded_projections_stable
#print axioms bounded_projections_sealed

end LeanProofs.IPRA.Foundations.RealizerProduct
