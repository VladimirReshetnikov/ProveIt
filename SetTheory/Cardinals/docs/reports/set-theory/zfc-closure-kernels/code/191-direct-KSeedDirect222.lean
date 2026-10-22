import BusyBeaver.ZFC.KSeedInterface222
import BusyBeaver.ZFC.Code254GIC

/-!
Direct seed semantics on the original model domain.

This implements the fresh-label proposal in
verification/k215/simplification/proposals/sharing-interfaces/calculus/DIRECT_FULL_SEED.md.
The first indiscernibility quotient is unnecessary: completeness supplies satisfaction of
the original named formulas, including literal equality. The later tagged quotient remains.
-/

namespace SetTheory.BusyBeaver.ZFC.KSeed222

open Tarski Code254 KCode222 NF BundleSemantics

universe u
variable {V : Type u}

/-- Equality interpretation preserves every free name of the original formula. -/
theorem free_th (f : NF) (i : Nat) (hi : NF.Free i f) : NF.Free i (KEind222.th f) := by
  induction f with
  | rel a b => exact hi
  | eq a b =>
      have ha := KEind222.aux_ne_l a b
      have hb := KEind222.aux_ne_r a b
      simp only [KEind222.th, KEind222.Eind, KEind222.Ev, KEind222.wa,
        KEind222.Bin, KEind222.Bout, KEind222.biff, NF.neg, NF.Free]
      rcases hi with rfl | rfl <;> simp_all
  | bot => exact hi.elim
  | imp f g hf hg => exact hi.elim (fun h => Or.inl (hf h)) (fun h => Or.inr (hg h))
  | all a f hf => exact ⟨hi.1, hf hi.2⟩

/-- A formula is fresh at the code of its equality interpretation. -/
theorem not_free_enc_th (f : NF) : ¬ NF.Free (enc (KEind222.th f)) f := by
  intro h
  have := Code254GIC.occurs_lt_enc (KEind222.th f) _ (NF.Free.occurs (free_th f _ h))
  omega

/-- The bundle constructors use membership atoms only. -/
theorem th_bundleNF (a b k : Nat) (m : NF) :
    KEind222.th (bundleNF a b k m) = bundleNF a b k (KEind222.th m) := by
  simp only [bundleNF, closNF, reqNF, negNF, KEind222.th]

namespace NamedBundleSemantics

theorem sat_negNF (mem : V → V → Prop) (e : Nat → V) (m : NF) :
    Tarski.Sat mem e (negNF m) ↔ ¬ Tarski.Sat mem e m := Iff.rfl

def matrix (mem : V → V → Prop) (e : Nat → V) (a b : Nat) (m : NF) (x y : V) : Prop :=
  Tarski.Sat mem (update (update e a x) b y) m

theorem sat_update (mem : V → V → Prop) (e : Nat → V) {k : Nat} {m : NF}
    (hfresh : ¬ NF.Free k m) (C : V) :
    Tarski.Sat mem (update e k C) m ↔ Tarski.Sat mem e m := by
  apply sat_ext
  intro n hn
  apply update_other
  intro hnk
  exact hfresh (hnk ▸ hn)

theorem req_iff (mem : V → V → Prop) (E : Nat → V) (b k : Nat) (hkb : k ≠ b) (m : NF) :
    Tarski.Sat mem E (reqNF b k m) ↔
      ∀ y, Tarski.Sat mem (update E b y) m →
        ∃ z, Tarski.Sat mem (update E b z) m ∧ mem z (E k) := by
  simp only [reqNF, sat_negNF, Tarski.Sat, update_idem, update_same,
    update_other _ _ hkb, neg_forall_imp]

theorem clos_iff (mem : V → V → Prop) (E : Nat → V) (a b k : Nat)
    (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b) (m : NF) :
    Tarski.Sat mem E (closNF a b k m) ↔
      ∀ y, mem y (E k) → ∃ x, matrix mem E a b m x y ∧
        ∀ x', (∀ w, mem w x' → mem w y) →
          ∀ y', matrix mem E a b m x' y' →
            ∃ z, matrix mem E a b m x' z ∧ mem z (E k) := by
  simp only [closNF, sat_negNF, Tarski.Sat, req_iff mem _ b k hkb,
    update_same, update_other _ _ hka, update_other _ _ hkb,
    update_other _ _ (Ne.symm hka), update_other _ _ (Ne.symm hkb),
    update_other _ _ (Ne.symm hab), update_idem, neg_forall_imp]
  simp only [matrix, update_swap _ hab, update_idem]

theorem matrix_marker (mem : V → V → Prop) (e : Nat → V) (a b k : Nat) (m : NF)
    (hka : k ≠ a) (hkb : k ≠ b) (hfresh : ¬ NF.Free k m) (C x y : V) :
    matrix mem (update e k C) a b m x y ↔ matrix mem e a b m x y := by
  simp only [matrix, update_swap _ hka, update_swap _ hkb, sat_update mem _ hfresh]

/-- Named falsity is actual falsity, so no irreflexivity premise is needed here. -/
theorem bundle_iff_seed (mem : V → V → Prop) (e : Nat → V) (a b k : Nat) (m : NF)
    (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b) (hfresh : ¬ NF.Free k m) :
    Tarski.Sat mem e (bundleNF a b k m) ↔
      SeedProp mem (matrix mem e a b m) (e a) := by
  have hRV : Tarski.Sat mem e (imp (rel a b) (all k (rel a b))) := by
    simp only [Tarski.Sat, update_other _ _ (Ne.symm hka), update_other _ _ (Ne.symm hkb)]
    exact fun h _ => h
  rw [bundleNF, sat_negNF]
  change (¬ (Tarski.Sat mem e (imp (rel a b) (all k (rel a b))) →
    ∀ C, Tarski.Sat mem (update e k C) (closNF a b k m) →
      ¬ Tarski.Sat mem (update e k C) (reqNF b k m))) ↔ _
  simp only [hRV, true_implies, neg_forall_imp, SeedProp]
  apply exists_congr
  intro C
  rw [clos_iff mem _ a b k hab hka hkb, req_iff mem _ b k hkb]
  simp only [matrix_marker mem e a b k m hka hkb hfresh, update_same]
  simp only [matrix, update_swap _ hkb, sat_update mem _ hfresh, update_self]
  exact and_comm

end NamedBundleSemantics

/-- All named relations, including literal equality, have seeds on the original domain. -/
theorem seed_direct (mem : V → V → Prop)
    (hT : ∀ f, DerivableNF f → ∀ e : Nat → V, Tarski.Sat mem e f)
    (ψ : NF) (e : Nat → V) :
    SeedProp mem (fun x y => Tarski.Sat mem (update (update e 0 x) 1 y) ψ) (e 0) := by
  let m := negNF (negNF ψ)
  let k := enc (KEind222.th m)
  have hk : 1 < k := by
    have hp := le_P_right (enc (negNF (KEind222.th ψ))) F
    change 1 < 4 * P (enc (negNF (KEind222.th ψ))) F
    unfold F at hp ⊢
    omega
  have hd : DerivableNF (bundleNF 0 1 k m) := by
    unfold DerivableNF
    rw [th_bundleNF]
    change C222 (enc (bundleNF 0 1 (enc (KEind222.th m)) (KEind222.th m)))
    rw [enc_bundleNF]
    exact C222.bundle 0 1 k (by omega) (by omega)
  have hs := (NamedBundleSemantics.bundle_iff_seed mem e 0 1 k m
    (by decide) (by omega) (by omega) (not_free_enc_th m)).mp (hT _ hd e)
  exact (seedProp_congr mem (e 0) (fun x y => by
    simp only [NamedBundleSemantics.matrix, m, negNF, Tarski.Sat]
    exact Classical.not_not)).mp hs

theorem fullSeed_direct_of_derivable (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (hT : ∀ f, DerivableNF f → ∀ e : Nat → V, Tarski.Sat mem e f) :
    KIndisc222.FullSeed mem := ⟨hirr, seed_direct mem hT⟩

#print axioms free_th
#print axioms NamedBundleSemantics.bundle_iff_seed
#print axioms seed_direct
#print axioms fullSeed_direct_of_derivable

end SetTheory.BusyBeaver.ZFC.KSeed222
