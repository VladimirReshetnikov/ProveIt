import BusyBeaver.ZFC.NamedNumeric254
import BusyBeaver.ZFC.Code254

/-!
Exact agreement of the two formalizations of the published four-tag calculus.

`Numeric254` is the attributed definition port from Mira-Cult's machine and
Jeff's verification at upstream commit
`297ab8df7e5de329605c3875b4934643b371a5e3`; `Code254` is the independent Lean
formalization of the same calculus. Their pairing functions agree, all nineteen
remaining expressions agree, and their twelve inference constructors give the
same proposition for every natural-number code. Zero and the gated bundle are
included without a freshness or positivity assumption beyond the actual gates.

The named encoders consequently agree as well. The existing exact refutation
equivalence for `NamedNumeric254.Q` can therefore use `Code254.C254 1`.
This identifies proof relations, not semantic model classes. In particular,
it does not compare encodable and decoded bundles, calibrate Q with ZFC, or
prove an enumerator, register-machine, binary simulation or endpoint theorem.
-/

namespace SetTheory.BusyBeaver.ZFC.NumericCode254

private theorem triangle_eq (n : Nat) : Numeric254.tri n = Cantor.tri n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Numeric254.tri, Cantor.tri, ih]
      omega

@[simp] theorem pairing_eq (a b : Nat) : Numeric254.P a b = Code254.P a b := by
  simp [Numeric254.P, Code254.P, Cantor.toNat, triangle_eq, Nat.add_comm]

@[simp] theorem wim_eq (a b : Nat) : Numeric254.wim a b = Code254.wim a b := by
  simp only [Numeric254.wim, Code254.wim, pairing_eq]

@[simp] theorem wel_eq (i j : Nat) : Numeric254.wel i j = Code254.wel i j := by
  simp only [Numeric254.wel, Code254.wel, pairing_eq]

@[simp] theorem wal_eq (i a : Nat) : Numeric254.wal i a = Code254.wal i a := by
  simp only [Numeric254.wal, Code254.wal, pairing_eq]

@[simp] theorem weq_eq (i j : Nat) : Numeric254.weq i j = Code254.weq i j := by
  simp only [Numeric254.weq, Code254.weq, pairing_eq]

@[simp] theorem falsity_eq : Numeric254.F = Code254.F := rfl

@[simp] theorem wn_eq (a : Nat) : Numeric254.wn a = Code254.wn a := by
  simp only [Numeric254.wn, Code254.wn, wim_eq, falsity_eq]

@[simp] theorem wa_eq (a b : Nat) : Numeric254.wa a b = Code254.wa a b := by
  simp only [Numeric254.wa, Code254.wa, wn_eq, wim_eq]

@[simp] theorem wex_eq (i a : Nat) : Numeric254.wex i a = Code254.wex i a := by
  simp only [Numeric254.wex, Code254.wex, wn_eq, wal_eq]

@[simp] theorem rho1_eq (a b : Nat) : Numeric254.rho1 a b = Code254.rho1 a b := by
  simp only [Numeric254.rho1, Code254.rho1, wex_eq, weq_eq]

@[simp] theorem rho2_eq (a b c : Nat) : Numeric254.rho2 a b c = Code254.rho2 a b c := by
  simp only [Numeric254.rho2, Code254.rho2, wim_eq, wal_eq]

@[simp] theorem rho3_eq (a b c : Nat) : Numeric254.rho3 a b c = Code254.rho3 a b c := by
  simp only [Numeric254.rho3, Code254.rho3, wim_eq, weq_eq, wel_eq]

@[simp] theorem rho4_eq (a b c : Nat) : Numeric254.rho4 a b c = Code254.rho4 a b c := by
  simp only [Numeric254.rho4, Code254.rho4, wim_eq, wal_eq]

@[simp] theorem rho5_eq (a b c : Nat) : Numeric254.rho5 a b c = Code254.rho5 a b c := by
  simp only [Numeric254.rho5, Code254.rho5, wim_eq, weq_eq, wel_eq]

@[simp] theorem rho6_eq (a b : Nat) : Numeric254.rho6 a b = Code254.rho6 a b := by
  simp only [Numeric254.rho6, Code254.rho6, wim_eq, wex_eq, wal_eq]

@[simp] theorem rho7_eq (a b c : Nat) : Numeric254.rho7 a b c = Code254.rho7 a b c := by
  simp only [Numeric254.rho7, Code254.rho7, wim_eq, weq_eq]

@[simp] theorem rho8_eq (a b c u : Nat) :
    Numeric254.rho8 a b c u = Code254.rho8 a b c u := by
  simp only [Numeric254.rho8, Code254.rho8, wim_eq]

@[simp] theorem bundleC_eq (a b c : Nat) :
    Numeric254.bundleC a b c = Code254.bundleC a b c := by
  simp only [Numeric254.bundleC, Code254.bundleC, wex_eq, wa_eq, wal_eq, wim_eq, wel_eq]

@[simp] theorem bundleG_eq (a b c : Nat) :
    Numeric254.bundleG a b c = Code254.bundleG a b c := by
  simp only [Numeric254.bundleG, Code254.bundleG, wex_eq, wa_eq, wal_eq, wim_eq, wel_eq]

@[simp] theorem bundle_eq (a b c : Nat) :
    Numeric254.bundle a b c = Code254.bundle a b c := by
  simp only [Numeric254.bundle, Code254.bundle, wa_eq, bundleC_eq, bundleG_eq,
    wim_eq, wel_eq, wal_eq, weq_eq]

/-- Every constructor of the attributed numerical calculus has the same code
and premises in the independent code calculus. -/
theorem c254_of_numThm {n : Nat} (h : Numeric254.NumThm n) : Code254.C254 n := by
  induction h with
  | truth => exact .truth
  | mp _ _ ihMinor ihMajor =>
      exact .mp ihMinor (by simpa only [wim_eq] using ihMajor)
  | gen i _ ih => simpa only [wal_eq] using Code254.C254.gen i ih
  | rho1 a b => simpa only [rho1_eq] using Code254.C254.r1 a b
  | rho2 a b c => simpa only [rho2_eq] using Code254.C254.r2 a b c
  | rho3 a b c => simpa only [rho3_eq] using Code254.C254.r3 a b c
  | rho4 a b c => simpa only [rho4_eq] using Code254.C254.r4 a b c
  | rho5 a b c => simpa only [rho5_eq] using Code254.C254.r5 a b c
  | rho6 a b => simpa only [rho6_eq] using Code254.C254.r6 a b
  | rho7 a b c => simpa only [rho7_eq] using Code254.C254.r7 a b c
  | rho8 a b c u => simpa only [rho8_eq] using Code254.C254.r8 a b c u
  | bundle a b c hca hcb =>
      simpa only [bundle_eq] using Code254.C254.bundle a b c hca hcb

/-- The reverse transport includes truth code0 and both exact bundle gates. -/
theorem numThm_of_c254 {n : Nat} (h : Code254.C254 n) : Numeric254.NumThm n := by
  induction h with
  | truth => exact .truth
  | mp _ _ ihMinor ihMajor =>
      exact .mp ihMinor (by simpa only [wim_eq] using ihMajor)
  | gen i _ ih => simpa only [wal_eq] using Numeric254.NumThm.gen i ih
  | r1 a b => simpa only [rho1_eq] using Numeric254.NumThm.rho1 a b
  | r2 a b c => simpa only [rho2_eq] using Numeric254.NumThm.rho2 a b c
  | r3 a b c => simpa only [rho3_eq] using Numeric254.NumThm.rho3 a b c
  | r4 a b c => simpa only [rho4_eq] using Numeric254.NumThm.rho4 a b c
  | r5 a b c => simpa only [rho5_eq] using Numeric254.NumThm.rho5 a b c
  | r6 a b => simpa only [rho6_eq] using Numeric254.NumThm.rho6 a b
  | r7 a b c => simpa only [rho7_eq] using Numeric254.NumThm.rho7 a b c
  | r8 a b c u => simpa only [rho8_eq] using Numeric254.NumThm.rho8 a b c u
  | bundle a b c hca hcb =>
      simpa only [bundle_eq] using Numeric254.NumThm.bundle a b c hca hcb

/-- Exact equality of the two derivability relations, for every code. -/
theorem numThm_iff_c254 (n : Nat) : Numeric254.NumThm n ↔ Code254.C254 n :=
  ⟨c254_of_numThm, numThm_of_c254⟩

@[simp] theorem encode_eq (f : Tarski.NF) :
    NamedNumeric254.encode f = Code254.enc f := by
  induction f with
  | bot => exact falsity_eq
  | rel i j => exact wel_eq i j
  | eq i j => exact weq_eq i j
  | imp a b ihA ihB =>
      simp only [NamedNumeric254.encode, Code254.enc, wim_eq, ihA, ihB]
  | all i a ih =>
      simp only [NamedNumeric254.encode, Code254.enc, wal_eq, ih]

/-- The already defined Q is also the theory of C254-derivable encodings. -/
theorem q_iff_c254 (f : Tarski.NF) :
    NamedNumeric254.Q f ↔ Code254.C254 (Code254.enc f) := by
  constructor
  · intro h
    simpa only [encode_eq] using c254_of_numThm h
  · intro h
    apply numThm_of_c254
    simpa only [encode_eq] using h

/-- Named transport through the same axiom-encoding obligation, now stated
directly using C254. This adds no theory calibration hypothesis or result. -/
theorem c254_of_named {Ax : Tarski.NF → Prop}
    (hAx : ∀ f, Ax f → Code254.C254 (Code254.enc f)) {f : Tarski.NF}
    (h : Tarski.Thm Ax f) : Code254.C254 (Code254.enc f) := by
  have hNumeric : Numeric254.NumThm (NamedNumeric254.encode f) :=
    NamedNumeric254.transport (fun g hg => by
      apply numThm_of_c254
      simpa only [encode_eq] using hAx g hg) h
  simpa only [encode_eq] using c254_of_numThm hNumeric

/-- The existing named refutation equivalence, with the common code relation. -/
theorem named_refutation_iff :
    Tarski.Thm NamedNumeric254.Q Tarski.NF.bot ↔ Code254.C254 1 :=
  NamedNumeric254.refutation_iff.trans (numThm_iff_c254 1)

end SetTheory.BusyBeaver.ZFC.NumericCode254
