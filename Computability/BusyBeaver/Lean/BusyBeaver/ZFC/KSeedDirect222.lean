import BusyBeaver.ZFC.KSeedInterface222

/-!
Direct full seed models from the named theory used by `c222_complete`.

Implements the previously uncompiled fresh-label proposal in
`verification/k215/simplification/proposals/sharing-interfaces/calculus/DIRECT_FULL_SEED.md`,
following the analogous Rocq `rocq224/src/Complete222.v` construction.
The semantic matrix keeps literal equality; its interpreted code is used only
to prove derivability and choose a fresh container label.
-/

namespace SetTheory.BusyBeaver.ZFC.KSeed222

open Tarski Code254 KCode222 NF BundleSemantics

universe u
variable {V : Type u}

/-- Every free name is strictly smaller than the code of its formula. -/
theorem free_lt_enc : ∀ (f : NF) (i : Nat), NF.Free i f → i < enc f
  | .rel a b, i, h => by
      have ha := le_P_left a b
      have hb := le_P_right a b
      simp only [NF.Free, enc, wel] at *
      omega
  | .eq a b, i, h => by
      have ha := le_P_left a b
      have hb := le_P_right a b
      simp only [NF.Free, enc, weq] at *
      omega
  | .bot, _, h => h.elim
  | .imp a b, i, h => by
      have ha := le_P_left (enc a) (enc b)
      have hb := le_P_right (enc a) (enc b)
      rcases h with h | h
      · have := free_lt_enc a i h
        change i < 4 * P (enc a) (enc b)
        omega
      · have := free_lt_enc b i h
        change i < 4 * P (enc a) (enc b)
        omega
  | .all a f, i, h => by
      have := free_lt_enc f i h.2
      have := le_P_right a (enc f)
      change i < 4 * P a (enc f) + 2
      omega

/-- Equality interpretation preserves each free name. -/
theorem free_th : ∀ (f : NF) (i : Nat), NF.Free i f → NF.Free i (KEind222.th f)
  | .rel _ _, _, h => h
  | .eq a b, i, h => by
      have ha := KEind222.aux_ne_l a b
      have hb := KEind222.aux_ne_r a b
      simp only [KEind222.th, KEind222.Eind, KEind222.Ev, KEind222.wa,
        KEind222.Bin, KEind222.Bout, KEind222.biff, NF.neg, NF.Free]
      rcases h with rfl | rfl <;> simp_all
  | .bot, _, h => h.elim
  | .imp a b, i, h => h.elim (fun h => Or.inl (free_th a i h))
      (fun h => Or.inr (free_th b i h))
  | .all a f, i, h => ⟨h.1, free_th f i h.2⟩

theorem th_bundleNF (a b k : Nat) (m : NF) :
    KEind222.th (bundleNF a b k m) = bundleNF a b k (KEind222.th m) := by
  simp only [bundleNF, closNF, reqNF, negNF, KEind222.th]

/-- Updating a name absent from the free support does not affect satisfaction. -/
theorem sat_update_fresh (mem : V → V → Prop) (m : NF) {k : Nat}
    (hfresh : ¬ NF.Free k m) (e : Nat → V) (d : V) :
    Tarski.Sat mem (update e k d) m ↔ Tarski.Sat mem e m := by
  apply sat_ext
  intro n hn
  exact update_other e d (fun h => hfresh (h ▸ hn))

theorem named_req_iff (mem : V → V → Prop) (E : Nat → V) (b k : Nat)
    (hkb : k ≠ b) (m : NF) :
    Tarski.Sat mem E (reqNF b k m) ↔
      ∀ y, Tarski.Sat mem (update E b y) m →
        ∃ z, Tarski.Sat mem (update E b z) m ∧ mem z (E k) := by
  simp only [reqNF, negNF, Tarski.Sat, update_idem, update_same,
    update_other _ _ hkb]
  exact forall_congr' fun _ => imp_congr_right fun _ => neg_forall_imp _ _

theorem named_clos_iff (mem : V → V → Prop) (E : Nat → V)
    (a b k : Nat) (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b) (m : NF) :
    Tarski.Sat mem E (closNF a b k m) ↔
      ∀ y, mem y (E k) → ∃ x,
        Tarski.Sat mem (update (update E a x) b y) m ∧
        ∀ x', (∀ w, mem w x' → mem w y) →
          ∀ y', Tarski.Sat mem (update (update E a x') b y') m →
            ∃ z, Tarski.Sat mem (update (update E a x') b z) m ∧ mem z (E k) := by
  simp only [closNF, negNF, Tarski.Sat, named_req_iff mem _ b k hkb,
    update_same, update_other _ _ hka, update_other _ _ hkb,
    update_other _ _ (Ne.symm hka), update_other _ _ (Ne.symm hkb),
    update_other _ _ (Ne.symm hab), update_idem]
  simp only [update_swap _ hab, update_idem]
  exact forall_congr' fun _ => imp_congr_right fun _ => neg_forall_imp _ _

/-- Named bundle semantics needs freshness, but no irreflexivity assumption. -/
theorem named_bundle_iff_seed (mem : V → V → Prop) (e : Nat → V)
    (a b k : Nat) (hab : a ≠ b) (hka : k ≠ a) (hkb : k ≠ b)
    (m : NF) (hfresh : ¬ NF.Free k m) :
    Tarski.Sat mem e (bundleNF a b k m) ↔
      SeedProp mem (fun x y => Tarski.Sat mem (update (update e a x) b y) m) (e a) := by
  have hRV : Tarski.Sat mem e (imp (rel a b) (all k (rel a b))) := by
    simp only [Tarski.Sat, update_other _ _ (Ne.symm hka),
      update_other _ _ (Ne.symm hkb)]
    exact fun h _ => h
  change (¬ (Tarski.Sat mem e (imp (rel a b) (all k (rel a b))) →
    Tarski.Sat mem e (all k (imp (closNF a b k m) (negNF (reqNF b k m)))))) ↔ _
  simp only [hRV, true_implies]
  change (¬ ∀ C, Tarski.Sat mem (update e k C) (closNF a b k m) →
    ¬ Tarski.Sat mem (update e k C) (reqNF b k m)) ↔ _
  rw [neg_forall_imp]
  unfold SeedProp
  apply exists_congr
  intro C
  rw [named_clos_iff mem _ a b k hab hka hkb, named_req_iff mem _ b k hkb]
  simp only [update_swap _ hka, update_swap _ hkb,
    sat_update_fresh mem m hfresh, update_same, update_self]
  exact and_comm

/-- The derivable named theory gives the full seed property on its original domain. -/
theorem seed_direct (mem : V → V → Prop)
    (hT : ∀ f, DerivableNF f → ∀ e : Nat → V, Tarski.Sat mem e f)
    (ψ : NF) (e : Nat → V) :
    SeedProp mem (fun x y => Tarski.Sat mem (update (update e 0 x) 1 y) ψ) (e 0) := by
  let m := negNF (negNF ψ)
  let k := enc (KEind222.th m)
  have hbig : 1 < k := by
    have h := le_P_right (enc (KEind222.th (negNF ψ))) F
    change 1 < 4 * P (enc (KEind222.th (negNF ψ))) F
    unfold F at h ⊢
    omega
  have hfresh : ¬ NF.Free k m := fun h =>
    Nat.lt_irrefl k (free_lt_enc _ k (free_th m k h))
  have hB : DerivableNF (bundleNF 0 1 k m) := by
    unfold DerivableNF
    rw [th_bundleNF]
    change C222 (enc (bundleNF 0 1 (enc (KEind222.th m)) (KEind222.th m)))
    rw [enc_bundleNF]
    exact C222.bundle 0 1 k (by omega) (by omega)
  have hs := (named_bundle_iff_seed mem e 0 1 k (by omega)
    (by omega) (by omega) m hfresh).mp (hT _ hB e)
  apply (seedProp_congr mem (e 0) (Q := fun x y =>
    Tarski.Sat mem (update (update e 0 x) 1 y) m) (fun x y => ?_)).mp hs
  simp only [m, negNF, Tarski.Sat]
  exact ⟨fun h => Classical.byContradiction fun hn => h hn, fun h hn => hn h⟩

#print axioms named_bundle_iff_seed
#print axioms seed_direct

end SetTheory.BusyBeaver.ZFC.KSeed222
