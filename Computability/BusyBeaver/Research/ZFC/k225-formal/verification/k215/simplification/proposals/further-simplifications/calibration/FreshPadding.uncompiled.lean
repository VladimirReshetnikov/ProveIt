import BusyBeaver.ZFC.KLowerQHyp

/-!
UNCOMPILED research proposal against beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc.
No new axioms, placeholders or admitted proofs. A compiler is not available locally.
This file demonstrates the small lower-model interface and fresh universal padding.
The first-stage seed adapter deliberately still uses the existing raw decoder theorem.
See NAMED_KERNEL.md for the separate obligation which removes that adapter entirely.
-/

namespace SetTheory.BusyBeaver.ZFC.KCalibrationSmall

open Tarski Tarski.NF Code254 KCode222 KSeed222
open LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u}

-- Reuse existing Code254GIC.occurs_lt_enc and not_free_enc.

/-- Named-formula freshness; no irreflexivity or equality-free restriction. -/
theorem sat_enc_agree (mem : V → V → Prop) (f : NF) (e e' : Nat → V)
    (h : ∀ i, i ≠ enc f → e i = e' i) : Tarski.Sat mem e f ↔ Tarski.Sat mem e' f := by
  apply sat_ext mem f e e'
  intro i hi
  exact h i (Nat.ne_of_lt (Code254GIC.occurs_lt_enc f i (Free.occurs hi)))

/-- One vacuous universal, rather than a classical double negation. -/
def pad (f : NF) : NF := all (enc f) f

theorem enc_pad_gt_one (f : NF) : 1 < enc (pad f) := by
  simp only [pad, enc, wal]
  omega

theorem eqFree_pad {f : NF} (h : KThmK.EqFree f) : KThmK.EqFree (pad f) := h

/-- Constructive semantic preservation, in any structure with the displayed valuation. -/
theorem sat_pad (mem : V → V → Prop) (f : NF) (e : Nat → V) :
    Tarski.Sat mem e (pad f) ↔ Tarski.Sat mem e f := by
  change (∀ d, Tarski.Sat mem (update e (enc f) d) f) ↔ Tarski.Sat mem e f
  constructor
  · intro h
    simpa only [KSeed222.update_self] using h (e (enc f))
  · intro h d
    apply (sat_enc_agree mem f e (update e (enc f) d) ?_).mp h
    intro i hi
    exact (update_other e d hi).symm

/-- A sparse axiom theory: one role-0/1 seed bundle per equality-free matrix. -/
def SeedAx (f : NF) : Prop :=
  ∃ ψ : NF, KThmK.EqFree ψ ∧ f = bundleNF 0 1 (enc (pad ψ)) (pad ψ)

theorem seedAx_derivable {f : NF} (h : SeedAx f) : DerivableNF f := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  unfold DerivableNF
  rw [th_eqFree _ (eqFree_bundleNF _ _ _ (eqFree_pad hψ)), enc_bundleNF]
  exact C222.bundle 0 1 (enc (pad ψ))
    (by have := enc_pad_gt_one ψ; omega) (by have := enc_pad_gt_one ψ; omega)

/-- Migration adapter. This theorem still uses semantic encode/decode equivalence. -/
theorem seed_of_seedAx_models (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hT : ∀ f, SeedAx f → ∀ e : Nat → V, Tarski.Sat mem e f)
    (ψ : NF) (hψ : KThmK.EqFree ψ) (e : Nat → V) :
    SeedProp mem (fun x y => Tarski.Sat mem (update (update e 0 x) 1 y) ψ) (e 0) := by
  have hbig := enc_pad_gt_one ψ
  have hB := hT _ ⟨ψ, hψ, rfl⟩ e
  have hs := seed_of_bundle mem hirr e 0 1 (enc (pad ψ))
    (by omega) (by omega) (by omega) (by
      rw [← enc_bundleNF]
      exact (Code254Models.sat_encode_decode mem hirr _ e).mpr hB)
  apply KLower.seedProp_congr (R := matrixRel mem e 0 1 (enc (pad ψ)))
    (R' := fun x y => Tarski.Sat mem (update (update e 0 x) 1 y) ψ) ?_ hs
  intro x y
  exact (Code254Models.sat_encode_decode mem hirr (pad ψ) _).trans (sat_pad mem ψ _)

/-- The original full theory of all derivable formulas is not needed by the lower endpoint. -/
theorem c222_of_zf_refutation_sparse
    (hf : BProv ZFax_s [] Form.fBot) : C222 F := by
  apply KEind222.c222_complete SeedAx (fun _ h => seedAx_derivable h)
  intro D mem hirr hT e
  have hfull := KIndisc222.fullSeed_quotient mem hirr
    (fun ψ hψ env => seed_of_seedAx_models mem hirr hT ψ hψ env)
  exact KLower.zf_consistent_of_formSeed (KLower.formSeed_of_fullSeed hfull)
    hfull.irr (KIndisc222.mk mem (e 0)) hf

#print axioms sat_pad
#print axioms c222_of_zf_refutation_sparse

end SetTheory.BusyBeaver.ZFC.KCalibrationSmall
