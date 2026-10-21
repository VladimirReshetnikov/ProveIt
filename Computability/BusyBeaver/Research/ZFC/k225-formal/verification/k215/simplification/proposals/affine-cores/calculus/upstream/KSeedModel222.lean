import BusyBeaver.ZFC.KSeed222
import BusyBeaver.ZFC.KEind222
import BusyBeaver.ZFC.Code254Models

/-!
The models that the completeness theorem of the 222/221 calculus quantifies over.

`seed_of_bundle` is the converse of `KSeed222.bundle_of_seed` for ordinary roles: in an
irreflexive structure a decoded seed bundle `dec (bundle222 a b c)` (with `a ≠ b`) says exactly
that the seed property holds for the relation its matrix `dec c` defines.

Take for `T` every named formula whose interpreted code is derivable (`DerivableNF`); then the
first premise of `KEind222.c222_complete` holds by definition. Every equality-free named formula
`ψ` is a matrix of some derivable bundle: its code `enc ψ` decodes back to `ψ` up to the alias
`⊥ ↦ x₀ ∈ x₀`, which an irreflexive structure cannot tell apart, and the equality interpretation
`th` fixes it. So a model of `T` has the seed property for every equality-free relation
(`seed_eqFree`).
-/

namespace SetTheory.BusyBeaver.ZFC.KSeed222

open SetTheory.BusyBeaver.ZFC.Tarski
open SetTheory.BusyBeaver.ZFC.Code254
open SetTheory.BusyBeaver.ZFC.KCode222
open SetTheory.BusyBeaver.ZFC.KThmK (EqFree)
open NF

universe u
variable {V : Type u}

theorem update_idem (e : Nat → V) (i : Nat) (d d' : V) : update (update e i d) i d' = update e i d' := by
  funext n; by_cases h : n = i <;> simp [update, h]

theorem update_self (e : Nat → V) (i : Nat) : update e i (e i) = e := by
  funext n; by_cases h : n = i
  · subst h; simp [update]
  · simp [update, h]

section Conv

variable (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
include hirr

/-- The request `req b c c` at `E`: an output of the current input, answered in `E c`. -/
theorem sat_req (E : Nat → V) (b c : Nat) (hcb : c ≠ b) :
    Tarski.Sat mem E (dec (req b c c)) ↔
      ∀ y, Tarski.Sat mem (update E b y) (dec c) →
        ∃ z, Tarski.Sat mem (update E b z) (dec c) ∧ mem z (E c) := by
  simp only [req, sat_wal, sat_wim, sat_wn mem hirr, sat_wel, update_idem, update_same,
    update_other _ _ hcb]
  refine forall_congr' fun y => imp_congr_right fun _ => ?_
  constructor
  · intro h
    exact Classical.byContradiction fun hne => h fun z hz hzc => hne ⟨z, hz, hzc⟩
  · rintro ⟨z, hz, hzc⟩ hall
    exact hall z hz hzc

/-- Reading the matrix at any valuation that agrees with the role assignment off the label. -/
theorem matrix_iff {e E : Nat → V} {a b c : Nat} {x y : V}
    (h : ∀ n, n ≠ c → E n = update (update e a x) b y n) :
    Tarski.Sat mem E (dec c) ↔ matrixRel mem e a b c x y :=
  sat_dec_agree mem c E _ h

/-- **The bundle gives the seed property** (ordinary roles). -/
theorem seed_of_bundle (e : Nat → V) (a b c : Nat) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (h : Tarski.Sat mem e (dec (bundle222 a b c))) :
    SeedProp mem (matrixRel mem e a b c) (e a) := by
  simp only [bundle222] at h
  rw [sat_wn mem hirr, sat_wim] at h
  have hN : ¬ Tarski.Sat mem e (dec (nks a b c)) := fun hn => h fun _ => hn
  simp only [nks] at hN
  rw [sat_wal] at hN
  obtain ⟨C, hC⟩ : ∃ C, ¬ Tarski.Sat mem (update e c C)
      (dec (wim (clos a b c c) (wn (req b c c)))) :=
    Classical.byContradiction fun hne => hN fun C => Classical.byContradiction fun hc => hne ⟨C, hc⟩
  rw [sat_wim, sat_wn mem hirr] at hC
  have hcl : Tarski.Sat mem (update e c C) (dec (clos a b c c)) :=
    Classical.byContradiction fun hn => hC fun h' => absurd h' hn
  have hrq : Tarski.Sat mem (update e c C) (dec (req b c c)) :=
    Classical.byContradiction fun hn => hC fun _ => hn
  have hac : a ≠ c := Ne.symm hca
  have hbc : b ≠ c := Ne.symm hcb
  have hba : b ≠ a := Ne.symm hab
  refine ⟨C, ?_, ?_⟩
  · -- the request at the input `e a`
    intro y hy
    have hy' : Tarski.Sat mem (update (update e c C) b y) (dec c) := by
      refine (matrix_iff mem hirr (x := e a) (y := y) ?_).mpr hy
      intro n hn
      by_cases hnb : n = b
      · subst hnb; simp [update, hn]
      · by_cases hna : n = a
        · subst hna; simp [update, hnb, hn]
        · simp [update, hnb, hna, hn]
    obtain ⟨z, hz, hzC⟩ := (sat_req mem hirr _ b c hcb).mp hrq y hy'
    refine ⟨z, (matrix_iff mem hirr ?_).mp hz, by rwa [update_same] at hzC⟩
    intro n hn
    by_cases hnb : n = b
    · subst hnb; simp [update, hn]
    · by_cases hna : n = a
      · subst hna; simp [update, hnb, hn]
      · simp [update, hnb, hna, hn]
  · -- the closure
    intro y hyC
    simp only [clos] at hcl
    rw [sat_wal] at hcl
    have h1 := hcl y
    rw [sat_wim, sat_wel, update_same, update_other _ _ hcb, update_same, sat_wn mem hirr,
      sat_wal] at h1
    obtain ⟨x, hx⟩ : ∃ x, ¬ Tarski.Sat mem (update (update (update e c C) b y) a x)
        (dec (wim c (wn (wal a (wim (wal c (wim (wel c a) (wel c b))) (req b c c)))))) :=
      Classical.byContradiction fun hne => h1 hyC fun x => Classical.byContradiction fun hc =>
        hne ⟨x, hc⟩
    rw [sat_wim, sat_wn mem hirr] at hx
    have hm : Tarski.Sat mem (update (update (update e c C) b y) a x) (dec c) :=
      Classical.byContradiction fun hn => hx fun h' => absurd h' hn
    have hall : Tarski.Sat mem (update (update (update e c C) b y) a x)
        (dec (wal a (wim (wal c (wim (wel c a) (wel c b))) (req b c c)))) :=
      Classical.byContradiction fun hn => hx fun _ => hn
    refine ⟨x, (matrix_iff mem hirr ?_).mp hm, ?_⟩
    · intro n hn
      by_cases hna : n = a
      · subst hna; simp [update, hab, hn]
      · by_cases hnb : n = b
        · subst hnb; simp [update, hna, hn]
        · simp [update, hna, hnb, hn]
    · intro x' hsub y' hy'
      rw [sat_wal] at hall
      have h3 := hall x'
      rw [sat_wim, update_idem] at h3
      have hsub' : Tarski.Sat mem (update (update (update e c C) b y) a x')
          (dec (wal c (wim (wel c a) (wel c b)))) := by
        rw [sat_wal]
        intro w
        rw [sat_wim, sat_wel, sat_wel, update_same, update_other _ _ hac, update_other _ _ hbc,
          update_same, update_other _ _ hba, update_same]
        exact hsub w
      have h4 := (sat_req mem hirr _ b c hcb).mp (h3 hsub')
      have hy'' : Tarski.Sat mem (update (update (update (update e c C) b y) a x') b y') (dec c) := by
        refine (matrix_iff mem hirr (x := x') (y := y') ?_).mpr hy'
        intro n hn
        by_cases hnb : n = b
        · subst hnb; simp [update, hn]
        · by_cases hna : n = a
          · subst hna; simp [update, hnb, hn]
          · simp [update, hnb, hna, hn]
      obtain ⟨z, hz, hzC⟩ := h4 y' hy''
      refine ⟨z, (matrix_iff mem hirr ?_).mp hz, ?_⟩
      · intro n hn
        by_cases hnb : n = b
        · subst hnb; simp [update, hn]
        · by_cases hna : n = a
          · subst hna; simp [update, hnb, hn]
          · simp [update, hnb, hna, hn]
      · rwa [update_other _ _ hca, update_other _ _ hcb, update_same] at hzC

end Conv

#print axioms seed_of_bundle

/-! ## Derivable bundles for every equality-free matrix -/

theorem enc_pos : ∀ f : NF, 0 < enc f
  | rel i j => by simp [enc, wel]
  | NF.eq i j => by simp [enc, weq]
  | NF.bot => by simp [enc, F]
  | imp a b => by
      have h1 := enc_pos a
      have h2 := le_P_left (enc a) (enc b)
      simp only [enc, wim]; omega
  | all i a => by simp [enc, wal]

/-- Codes of named formulas decode back, up to the alias `⊥ ↦ x₀ ∈ x₀`, which re-encodes to `F`. -/
theorem enc_dec_enc : ∀ f : NF, enc (dec (enc f)) = enc f
  | rel i j => by simp only [enc]; rw [dec_wel]; rfl
  | NF.eq i j => by simp only [enc]; rw [dec_weq]; rfl
  | NF.bot => by simp only [enc]; rw [dec_F]; exact wel_zero_zero
  | imp a b => by
      have h := enc_pos a
      simp only [enc]
      rw [dec_wim (by omega)]
      simp only [enc, enc_dec_enc a, enc_dec_enc b]
  | all i a => by
      simp only [enc]
      rw [dec_wal]
      simp only [enc, enc_dec_enc a]

theorem eqFree_dec_enc : ∀ f : NF, EqFree f → EqFree (dec (enc f))
  | rel i j, _ => by simp only [enc]; rw [dec_wel]; trivial
  | NF.eq _ _, h => h.elim
  | NF.bot, _ => by simp only [enc]; rw [dec_F]; trivial
  | imp a b, h => by
      have hp := enc_pos a
      simp only [enc]
      rw [dec_wim (by omega)]
      exact ⟨eqFree_dec_enc a h.1, eqFree_dec_enc b h.2⟩
  | all i a, h => by
      simp only [enc]
      rw [dec_wal]
      exact eqFree_dec_enc a h

theorem th_eqFree : ∀ f : NF, EqFree f → KEind222.th f = f
  | rel _ _, _ => rfl
  | NF.eq _ _, h => h.elim
  | NF.bot, _ => rfl
  | imp a b, h => by simp only [KEind222.th, th_eqFree a h.1, th_eqFree b h.2]
  | all i a, h => by simp only [KEind222.th, th_eqFree a h]

/-- The bundle as a named formula with container `k` and matrix `m`. -/
def negNF (x : NF) : NF := imp x NF.bot

def reqNF (b k : Nat) (m : NF) : NF := all b (imp m (negNF (all b (imp m (negNF (rel b k))))))

def closNF (a b k : Nat) (m : NF) : NF :=
  all b (imp (rel b k) (negNF (all a (imp m (negNF (all a (imp (all k (imp (rel k a) (rel k b)))
    (reqNF b k m))))))))

def bundleNF (a b k : Nat) (m : NF) : NF :=
  negNF (imp (imp (rel a b) (all k (rel a b))) (all k (imp (closNF a b k m) (negNF (reqNF b k m)))))

theorem enc_bundleNF (a b : Nat) (m : NF) : enc (bundleNF a b (enc m) m) = bundle222 a b (enc m) := by
  simp only [bundleNF, closNF, reqNF, negNF, enc, bundle222, nks, clos, req, vrel, wn]

theorem eqFree_bundleNF (a b k : Nat) {m : NF} (hm : EqFree m) : EqFree (bundleNF a b k m) := by
  simp [bundleNF, closNF, reqNF, negNF, EqFree, hm]

/-- Named formulas whose interpreted codes are derivable in the 222/221 calculus. -/
def DerivableNF (f : NF) : Prop := C222 (enc (KEind222.th f))

theorem derivable_bundle (ψ : NF) (hψ : EqFree ψ) (a b : Nat) (ha : enc ψ ≠ a) (hb : enc ψ ≠ b) :
    DerivableNF (dec (bundle222 a b (enc ψ))) := by
  unfold DerivableNF
  rw [← enc_bundleNF, th_eqFree _ (eqFree_dec_enc _ (eqFree_bundleNF _ _ _ hψ)), enc_dec_enc,
    enc_bundleNF]
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
    have h1 := enc_pos ψ
    have h2 := le_P_left (enc (negNF ψ)) F
    have h3 := le_P_left (enc ψ) F
    simp only [ψ', negNF, enc, wim] at h2 h3 ⊢; omega
  have hs := seed_of_bundle mem hirr e 0 1 (enc ψ') (by omega) (by omega) (by omega)
    (hT _ (derivable_bundle ψ' hψ' 0 1 (by omega) (by omega)) e)
  obtain ⟨C, h1, h2⟩ := hs
  have hiff : ∀ x y, matrixRel mem e 0 1 (enc ψ') x y ↔ Tarski.Sat mem (update (update e 0 x) 1 y) ψ := by
    intro x y
    unfold matrixRel
    rw [Code254Models.sat_encode_decode mem hirr]
    simp only [ψ', negNF, Tarski.Sat]
    exact ⟨fun h => Classical.byContradiction fun hn => h hn, fun h h' => h' h⟩
  refine ⟨C, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨z, hz, hzC⟩ := h1 y ((hiff _ _).mpr hy)
    exact ⟨z, (hiff _ _).mp hz, hzC⟩
  · obtain ⟨x, hx, hsub⟩ := h2 y hy
    refine ⟨x, (hiff _ _).mp hx, fun x' hx' y' hy' => ?_⟩
    obtain ⟨z, hz, hzC⟩ := hsub x' hx' y' ((hiff _ _).mpr hy')
    exact ⟨z, (hiff _ _).mp hz, hzC⟩

#print axioms seed_eqFree

end SetTheory.BusyBeaver.ZFC.KSeed222

