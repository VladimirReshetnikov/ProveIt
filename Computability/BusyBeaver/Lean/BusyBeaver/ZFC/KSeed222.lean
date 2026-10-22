import BusyBeaver.ZFC.KCode222

/-!
Semantics of the decoded seed bundle of the 222/221 calculus.

`SeedProp mem Q A` is Elliot Glazer's seed form of K for a binary relation `Q` (input, output)
and an input `A`: there is a container `C` that

* answers the seed request: if `A` has a `Q`-output, some output of `A` lies in `C`;
* consists of outputs (each member of `C` is an output of some input), each of whose subsets
  has its request answered in `C`.

`bundle_of_seed`: in an irreflexive structure, if `SeedProp` holds for the relation that the
decoded matrix `dec c` defines at roles `a` (input) and `b` (output), then the decoded bundle
`dec (bundle222 a b c)` holds. Both the ordinary roles (`a ≠ b`) and the degenerate ones are
covered; the label `c` is never free in its own decoded matrix (`sat_dec_agree`).
-/

set_option maxRecDepth 2048

namespace SetTheory.BusyBeaver.ZFC.KSeed222

open SetTheory.BusyBeaver.ZFC.Tarski
open SetTheory.BusyBeaver.ZFC.Code254
open SetTheory.BusyBeaver.ZFC.KCode222
open NF

universe u
variable {V : Type u}

/-! ## The label is not free in its own decoded matrix -/

theorem decF_occurs : ∀ (f n i : Nat), Occurs i (decF f n) → i = 0 ∨ i < n
  | 0, _, i, h | _ + 1, 0, i, h => by
      simp only [decF, T0, Occurs] at h; omega
  | f + 1, n + 1, i, h => by
      have hz := ofNat_le ((n + 1) / 4)
      have hd : (n + 1) / 4 < n + 1 := Nat.div_lt_self (by omega) (by omega)
      simp only [decF] at h
      split at h
      · simp only [Occurs] at h
        rcases h with h | h <;> rcases decF_occurs f _ i h with h | h <;> omega
      · simp only [Occurs] at h; omega
      · simp only [Occurs] at h
        rcases h with h | h
        · omega
        · rcases decF_occurs f _ i h with h | h <;> omega
      · simp only [Occurs] at h; omega

/-- Truth of `dec c` does not depend on the value of the name `c`. -/
theorem sat_dec_agree (mem : V → V → Prop) (c : Nat) (e1 e2 : Nat → V)
    (h : ∀ n, n ≠ c → e1 n = e2 n) :
    Tarski.Sat mem e1 (dec c) ↔ Tarski.Sat mem e2 (dec c) := by
  by_cases hc : c = 0
  · subst hc
    exact ⟨fun _ h => h, fun _ h => h⟩
  · apply sat_ext
    exact fun n hn => h n fun hnc => by
      subst hnc; rcases decF_occurs (n + 1) n n (Free.occurs hn) with h0 | h0 <;> omega

/-! ## The seed property -/

/-- Glazer's seed form of K for the relation `Q` (input, output) at input `A`. -/
def SeedProp (mem : V → V → Prop) (Q : V → V → Prop) (A : V) : Prop :=
  ∃ C, (∀ y, Q A y → ∃ z, Q A z ∧ mem z C) ∧
    ∀ y, mem y C → ∃ x, Q x y ∧
      ∀ x', (∀ w, mem w x' → mem w y) → ∀ y', Q x' y' → ∃ z, Q x' z ∧ mem z C

/-- The relation that the decoded matrix `dec c` defines at input `a` and output `b`. -/
def matrixRel (mem : V → V → Prop) (e : Nat → V) (a b c : Nat) (x y : V) : Prop :=
  Tarski.Sat mem (update (update e a x) b y) (dec c)

/-! ## Shared semantic normalization -/

/-- The seed property depends only on the binary relation's truth values. -/
theorem seedProp_congr (mem : V → V → Prop) (A : V) {Q Q' : V → V → Prop}
    (hQ : ∀ x y, Q x y ↔ Q' x y) : SeedProp mem Q A ↔ SeedProp mem Q' A := by
  simp only [SeedProp, hQ]

namespace BundleSemantics

theorem update_idem (e : Nat → V) (i : Nat) (d d' : V) :
    update (update e i d) i d' = update e i d' := by
  funext n; by_cases h : n = i <;> simp [update, h]

theorem update_swap (e : Nat → V) {i j : Nat} (hij : i ≠ j) (d d' : V) :
    update (update e i d) j d' = update (update e j d') i d := by
  funext n; by_cases hi : n = i <;> by_cases hj : n = j <;> simp_all [update]

theorem update_self (e : Nat → V) (i : Nat) : update e i (e i) = e := by
  funext n; by_cases h : n = i <;> simp_all [update]

theorem sat_dec_update (mem : V → V → Prop) (e : Nat → V) (c : Nat) (d : V) :
    Tarski.Sat mem (update e c d) (dec c) ↔ Tarski.Sat mem e (dec c) :=
  sat_dec_agree mem c _ _ fun _ hn => update_other _ _ hn

theorem neg_forall_imp (P Q : V → Prop) :
    (¬ ∀ x, P x → ¬ Q x) ↔ ∃ x, P x ∧ Q x :=
  ⟨fun h => Classical.byContradiction fun hn => h fun x hx hq => hn ⟨x, hx, hq⟩,
    fun ⟨x, hx, hq⟩ h => h x hx hq⟩

theorem req_iff (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (E : Nat → V) (b c : Nat) (hcb : c ≠ b) :
    Tarski.Sat mem E (dec (req b c c)) ↔
      ∀ y, Tarski.Sat mem (update E b y) (dec c) →
        ∃ z, Tarski.Sat mem (update E b z) (dec c) ∧ mem z (E c) := by
  simp only [req, sat_wal, sat_wim, sat_wn mem hirr, sat_wel,
    update_idem, update_same, update_other _ _ hcb, neg_forall_imp]

theorem clos_iff (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (E : Nat → V) (a b c : Nat) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    Tarski.Sat mem E (dec (clos a b c c)) ↔
      ∀ y, mem y (E c) → ∃ x, matrixRel mem E a b c x y ∧
        ∀ x', (∀ w, mem w x' → mem w y) →
          ∀ y', matrixRel mem E a b c x' y' →
            ∃ z, matrixRel mem E a b c x' z ∧ mem z (E c) := by
  simp only [clos, sat_wal, sat_wim, sat_wn mem hirr, sat_wel, req_iff mem hirr _ b c hcb,
    update_same, update_other _ _ hca, update_other _ _ hcb,
    update_other _ _ (Ne.symm hca), update_other _ _ (Ne.symm hcb),
    update_other _ _ (Ne.symm hab), update_idem, neg_forall_imp]
  simp only [matrixRel, update_swap _ hab, update_idem]

theorem matrix_marker (mem : V → V → Prop) (e : Nat → V) (a b c : Nat)
    (hca : c ≠ a) (hcb : c ≠ b) (C x y : V) :
    matrixRel mem (update e c C) a b c x y ↔ matrixRel mem e a b c x y := by
  simp only [matrixRel, update_swap _ hca, update_swap _ hcb, sat_dec_update]

theorem bundle_iff_seed (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (e : Nat → V) (a b c : Nat) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    Tarski.Sat mem e (dec (bundle222 a b c)) ↔
      SeedProp mem (matrixRel mem e a b c) (e a) := by
  have hRV : Tarski.Sat mem e (dec (vrel a b c)) := by
    simp only [vrel, sat_wim, sat_wal, sat_wel,
      update_other _ _ (Ne.symm hca), update_other _ _ (Ne.symm hcb)]
    exact fun h _ => h
  simp only [bundle222, sat_wn mem hirr, sat_wim, hRV, true_implies, nks, sat_wal,
    neg_forall_imp, SeedProp]
  refine exists_congr fun C => ?_
  rw [clos_iff mem hirr _ a b c hab hca hcb, req_iff mem hirr _ b c hcb]
  simp only [matrix_marker mem e a b c hca hcb, update_same]
  simp only [matrixRel, update_swap _ hcb, sat_dec_update, update_self]
  exact and_comm

theorem diagonal_bundle_of_seed (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (e : Nat → V) (a c : Nat) (hca : c ≠ a)
    (h : SeedProp mem (matrixRel mem e a a c) (e a)) :
    Tarski.Sat mem e (dec (bundle222 a a c)) := by
  obtain ⟨C, hroot, hcl⟩ := h
  have hr : Tarski.Sat mem (update e c C) (dec (req a c c)) := by
    rw [req_iff mem hirr _ a c hca]
    simpa only [matrixRel, update_self, update_idem, update_swap _ hca,
      sat_dec_update, update_same] using hroot
  have hc : Tarski.Sat mem (update e c C) (dec (clos a a c c)) := by
    simp only [clos, sat_wal, sat_wim, sat_wn mem hirr, sat_wel,
      req_iff mem hirr _ a c hca, update_same,
      update_other _ _ (Ne.symm hca), update_idem, neg_forall_imp,
      update_swap _ hca, sat_dec_update]
    intro y hy
    obtain ⟨x, hx, _⟩ := hcl y hy
    refine ⟨y, ?_, fun x' _ => ?_⟩
    · simpa only [matrixRel, update_idem] using hx
    · simpa only [matrixRel, update_idem] using hroot
  have hRV : Tarski.Sat mem e (dec (vrel a a c)) := by
    simp only [vrel, sat_wim, sat_wal, sat_wel, update_other _ _ (Ne.symm hca)]
    exact fun h _ => h
  simp only [bundle222, sat_wn mem hirr, sat_wim, hRV, true_implies,
    nks, sat_wal, neg_forall_imp]
  exact ⟨C, hc, hr⟩

end BundleSemantics

/-- The decoded bundle follows from the seed property, including coincident input/output roles. -/
theorem bundle_of_seed (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (e : Nat → V) (a b c : Nat) (hca : c ≠ a) (hcb : c ≠ b)
    (h : SeedProp mem (matrixRel mem e a b c) (e a)) :
    Tarski.Sat mem e (dec (bundle222 a b c)) := by
  by_cases hab : a = b
  · subst b; exact BundleSemantics.diagonal_bundle_of_seed mem hirr e a c hca h
  · exact (BundleSemantics.bundle_iff_seed mem hirr e a b c hab hca hcb).mpr h

#print axioms BundleSemantics.bundle_iff_seed
#print axioms bundle_of_seed

end SetTheory.BusyBeaver.ZFC.KSeed222
