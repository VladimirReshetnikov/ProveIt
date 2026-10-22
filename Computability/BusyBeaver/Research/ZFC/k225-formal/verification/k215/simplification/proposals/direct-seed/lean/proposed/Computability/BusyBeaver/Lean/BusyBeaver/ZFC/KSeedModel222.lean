import BusyBeaver.ZFC.KSeedInterface222
import BusyBeaver.ZFC.Code254Models

/-!
The models that the completeness theorem of the 222/221 calculus quantifies over.

`seed_of_bundle` is the converse of `KSeed222.bundle_of_seed` for ordinary roles: in an
irreflexive structure a decoded seed bundle `dec (bundle222 a b c)` (with `a ≠ b`) says exactly
that the seed property holds for the relation its matrix `dec c` defines.

Take for `T` every named formula whose interpreted code is derivable (`DerivableNF`); then the
first premise of `KEind222.c222_complete` holds by definition. Every equality-free named formula
`ψ` is the matrix of a derivable named bundle (`derivable_named_bundle`), whose decoded code means
the same in an irreflexive structure (`Code254Models.sat_encode_decode`), and the equality
interpretation `th` fixes it. So a model of `T` has the seed property for every equality-free
relation (`seed_eqFree`).

The semantic round trip retains the phase-six adaptation of the affine-cores packet
(aa66d0a33f), extending the structural proposal; the shared bundle semantics `BundleSemantics.bundle_iff_seed` and `seedProp_congr`
(proposal semantic-normal-forms) replace the separate decoding of the reverse direction.
-/

namespace SetTheory.BusyBeaver.ZFC.KSeed222

open SetTheory.BusyBeaver.ZFC.Tarski
open SetTheory.BusyBeaver.ZFC.Code254
open SetTheory.BusyBeaver.ZFC.KCode222
open SetTheory.BusyBeaver.ZFC.KThmK (EqFree)
open NF

universe u
variable {V : Type u}

section Conv

variable (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
include hirr

/-- **The bundle gives the seed property** (ordinary roles). -/
theorem seed_of_bundle (e : Nat → V) (a b c : Nat) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (h : Tarski.Sat mem e (dec (bundle222 a b c))) :
    SeedProp mem (matrixRel mem e a b c) (e a) :=
  (BundleSemantics.bundle_iff_seed mem hirr e a b c hab hca hcb).mp h

end Conv

#print axioms seed_of_bundle

/-! ## Derivable bundles for every equality-free matrix -/

/-- Equality interpretation fixes equality-free named formulas. -/
theorem th_eqFree : ∀ f : NF, EqFree f → KEind222.th f = f
  | rel _ _, _ => rfl
  | NF.eq _ _, h => h.elim
  | NF.bot, _ => rfl
  | imp a b, h => by simp only [KEind222.th, th_eqFree a h.1, th_eqFree b h.2]
  | all i a, h => by simp only [KEind222.th, th_eqFree a h]

theorem eqFree_bundleNF (a b k : Nat) {m : NF} (hm : EqFree m) : EqFree (bundleNF a b k m) := by
  simp [bundleNF, closNF, reqNF, negNF, EqFree, hm]

theorem derivable_named_bundle (ψ : NF) (hψ : EqFree ψ) (a b : Nat)
    (ha : enc ψ ≠ a) (hb : enc ψ ≠ b) :
    DerivableNF (bundleNF a b (enc ψ) ψ) := by
  unfold DerivableNF
  rw [th_eqFree _ (eqFree_bundleNF _ _ _ hψ), enc_bundleNF]
  exact C222.bundle a b (enc ψ) ha hb

/-- **A model of the derivable formulas has the seed property for every equality-free relation**,
with input name `0`, output name `1` and the other names as parameters. -/
theorem seed_eqFree (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hT : ∀ f, DerivableNF f → ∀ e : Nat → V, Tarski.Sat mem e f) (ψ : NF) (hψ : EqFree ψ)
    (e : Nat → V) : SeedProp mem (fun x y => Tarski.Sat mem (update (update e 0 x) 1 y) ψ) (e 0) := by
  -- double negation keeps the matrix's meaning and moves its code past the role names
  let ψ' := negNF (negNF ψ)
  have hψ' : EqFree ψ' := ⟨⟨hψ, trivial⟩, trivial⟩
  have hbig : 1 < enc ψ' := by
    have h := le_P_right (enc (negNF ψ)) F
    change 1 < 4 * P (enc (negNF ψ)) F
    unfold F at h ⊢
    omega
  have hs := seed_of_bundle mem hirr e 0 1 (enc ψ') (by omega) (by omega) (by omega)
    (by
      rw [← enc_bundleNF]
      exact (Code254Models.sat_encode_decode mem hirr _ e).mpr
        (hT _ (derivable_named_bundle ψ' hψ' 0 1 (by omega) (by omega)) e))
  have hiff : ∀ x y, matrixRel mem e 0 1 (enc ψ') x y ↔ Tarski.Sat mem (update (update e 0 x) 1 y) ψ := by
    intro x y
    unfold matrixRel
    rw [Code254Models.sat_encode_decode mem hirr]
    simp only [ψ', negNF, Tarski.Sat]
    exact ⟨fun h => Classical.byContradiction fun hn => h hn, fun h h' => h' h⟩
  exact (seedProp_congr mem (e 0) hiff).mp hs

#print axioms seed_eqFree

end SetTheory.BusyBeaver.ZFC.KSeed222
