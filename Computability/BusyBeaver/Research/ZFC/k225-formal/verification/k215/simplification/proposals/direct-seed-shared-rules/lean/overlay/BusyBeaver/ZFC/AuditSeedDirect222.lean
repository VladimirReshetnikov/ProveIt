import BusyBeaver.ZFC.KEndpoint

/-! Typed clients for the direct seed bridge and the unchanged generic endpoint.
No machine-specific K215 certificates are imported by this audit. -/
namespace SetTheory.BusyBeaver.ZFC.AuditSeedDirect222
open KZip KRuntimeCore KDenseBridge LeanProofs.BoundedZFCConsistency

example {V : Type} (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hT : ∀ f, KSeed222.DerivableNF f → ∀ e : Nat → V, Tarski.Sat mem e f) :
    KIndisc222.FullSeed mem := KIndisc222.fullSeed_direct_of_derivable mem hirr hT

example : KCode222.C222 Code254.F ↔ BProv ZFax_s [] Form.fBot :=
  KEndpoint.c222_iff_zf_refutation

example {m : Nat} {D : Machine (m + 1)} {M : TMN} {ex : Nat → Nat}
    {p : RegisterPath.Program} {T : Conf} {R0 : RegisterPath.Registers}
    (hD : Commutes D M ex 230) (hH : ∀ b, M 230 b = none)
    (hB : BoxLemmas M) (hcov : KSim.Covered M p)
    (hboot : Reach M (zc (ex 0) [] []) T) (hrel : KSim.Rel p ⟨[], R0⟩ T)
    (hsrc : RegisterPath.Halts p ⟨[], R0⟩ ↔ KCode222.C222 Code254.F) :
    BlankHalts D ↔ BProv ZFCax_s [] Form.fBot :=
  KEndpoint.blank_halts_iff_zfc_refutation hD hH hB hcov hboot hrel hsrc

#print axioms KSeed222.free_lt_enc
#print axioms KSeed222.free_th
#print axioms KSeed222.named_bundle_iff_seed
#print axioms KSeed222.seed_direct
#print axioms KIndisc222.fullSeed_direct_of_derivable
#print axioms KLower.formSeed_of_fullSeed
#print axioms KEndpoint.c222_of_zf_refutation
#print axioms KEndpoint.c222_iff_zf_refutation
#print axioms KEndpoint.blank_halts_iff_zfc_refutation

end SetTheory.BusyBeaver.ZFC.AuditSeedDirect222
