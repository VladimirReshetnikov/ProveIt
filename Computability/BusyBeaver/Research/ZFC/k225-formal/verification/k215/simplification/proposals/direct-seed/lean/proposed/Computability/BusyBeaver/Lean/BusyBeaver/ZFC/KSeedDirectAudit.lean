import BusyBeaver.ZFC.KEndpoint
import BusyBeaver.ZFC.KIndisc222

/-! Typed acceptance clients for the direct-seed refactor.

The generic endpoint has the same public type. The two old model constructors
remain available with their original statements through the compatibility modules.
-/

namespace SetTheory.BusyBeaver.ZFC.KSeedDirectAudit

open KZip KRuntimeCore KDenseBridge LeanProofs.BoundedZFCConsistency

theorem lower_unchanged (h : BProv ZFax_s [] Form.fBot) : KCode222.C222 Code254.F :=
  KEndpoint.c222_of_zf_refutation h

theorem calibration_unchanged : KCode222.C222 Code254.F ↔ BProv ZFax_s [] Form.fBot :=
  KEndpoint.c222_iff_zf_refutation

theorem endpoint_unchanged
    {m : Nat} {D : Machine (m + 1)} {M : TMN} {ex : Nat → Nat} {p : RegisterPath.Program}
    {T : Conf} {R0 : RegisterPath.Registers} (hD : Commutes D M ex 230)
    (hH : ∀ b, M 230 b = none) (hB : BoxLemmas M) (hcov : KSim.Covered M p)
    (hboot : Reach M (zc (ex 0) [] []) T) (hrel : KSim.Rel p ⟨[], R0⟩ T)
    (hsrc : RegisterPath.Halts p ⟨[], R0⟩ ↔ KCode222.C222 Code254.F) :
    BlankHalts D ↔ BProv ZFCax_s [] Form.fBot :=
  KEndpoint.blank_halts_iff_zfc_refutation hD hH hB hcov hboot hrel hsrc

universe u
variable {V : Type u}

theorem direct_seed (mem : V → V → Prop)
    (hT : ∀ f, KSeed222.DerivableNF f → ∀ e : Nat → V, Tarski.Sat mem e f)
    (ψ : Tarski.NF) (e : Nat → V) :
    KSeed222.SeedProp mem
      (fun x y => Tarski.Sat mem (Tarski.update (Tarski.update e 0 x) 1 y) ψ) (e 0) :=
  KSeed222.seed_direct mem hT ψ e

theorem legacy_seed (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hT : ∀ f, KSeed222.DerivableNF f → ∀ e : Nat → V, Tarski.Sat mem e f)
    (ψ : Tarski.NF) (hψ : KThmK.EqFree ψ) (e : Nat → V) :
    KSeed222.SeedProp mem
      (fun x y => Tarski.Sat mem (Tarski.update (Tarski.update e 0 x) 1 y) ψ) (e 0) :=
  KSeed222.seed_eqFree mem hirr hT ψ hψ e

theorem legacy_quotient (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hT : ∀ f, KSeed222.DerivableNF f → ∀ e : Nat → V, Tarski.Sat mem e f) :
    KIndisc222.FullSeed (KIndisc222.qmem mem) :=
  KIndisc222.fullSeed_of_derivable mem hirr hT

#print axioms lower_unchanged
#print axioms calibration_unchanged
#print axioms endpoint_unchanged
#print axioms direct_seed
#print axioms legacy_seed
#print axioms legacy_quotient

end SetTheory.BusyBeaver.ZFC.KSeedDirectAudit
