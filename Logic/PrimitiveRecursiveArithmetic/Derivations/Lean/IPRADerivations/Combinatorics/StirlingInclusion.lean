import IPRADerivations.Combinatorics.BellPascalInversion
import IPRADerivations.Combinatorics.CatalanBallot
import IPRADerivations.Combinatorics.StirlingBinomial
import IPRADerivations.Combinatorics.BellStirling
import IPRADerivations.AnalyticNumberTheory.Totient

/-!
# Inclusion–exclusion for the Stirling numbers

Packet: `combinatorics/bell_numbers_ipra`, Theorem `thm:finite-dobinski` (the identity
`eq:stirling-ie`): for all `n, k`,

  `k! S(n, k) = ∑_{i ≤ k} (−1)^{k−i} C(k, i) iⁿ`,

with the signed sum split by the parity of `k − i` into natural numbers `E⁺(n, k)` (even) and
`E⁻(n, k)` (odd), so the statement is `k! S(n, k) + E⁻(n, k) = E⁺(n, k)`.

* `gb_ratio`, `gb_absorb`: `(k − j) C(k, j) = (j + 1) C(k, j + 1)` and
  `i C(k + 1, i) + (k + 1) C(k, i) = (k + 1) C(k + 1, i)` for the guarded binomial `gb`;
* `step_e`, `step_o`, `Ep_step`, `Om_step`: `E^±(n + 1, k + 1) + (k + 1) E^∓(n, k) = (k + 1) E^±(n, k + 1)`
  (pointwise absorption and the parity flip; `sum_affine` combines sums with different parameters);
* `alt_e`, `alt_o`, `base`: `E⁺(0, k + 1) = E⁻(0, k) + E⁺(0, k)` and `E⁻(0, k + 1) = E⁺(0, k) + E⁻(0, k)`
  (Pascal's rule after shifting the index), so `∑_i (−1)^{k−i} C(k, i) = [k = 0]` and the case `n = 0` holds;
* `q_eq`, `bell_ie` (`eq:bell-ie`): `(E⁺ ∸ E⁻)/k! = S(n, k)` exactly, so `B_n = ∑_{k ≤ n} (E⁺(n, k) ∸ E⁻(n, k))/k!`;
* `pt_zero`, `pt_succ`, `stirling_ie`: induction on `n` for all `k` at once, as the vanishing of the violation
  count over `k ≤ K`, from `S(n + 1, k + 1) = (k + 1) S(n, k + 1) + S(n, k)` and `(k + 1)! = k! (k + 1)`.

The finite Dobinski form `eq:bell-finite-dobinski` is in `Combinatorics/BellDobinski`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.StirlingInclusion

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Combinatorics.Stirling (gle gle_of_le stir)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_zero gb_self gb_above gb_pascal)
open LeanProofs.IPRA.Combinatorics.CatalanBallot (binom_ratio)
open LeanProofs.IPRA.Combinatorics.BellPascalInversion (ev od congrEv congrOd ev_succ od_succ ev_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Guarded binomial identities -/

/-- `(k − j) C(k, j) = (j + 1) C(k, j + 1)`. -/
theorem gb_ratio (k j : PTm n) : Γ ⊢[PRAAx] monus k j * gb k j ≐ succ j * gb k (succ j) := by
  refine .orE (lt_or_le j k) ?_ ?_
  · have h : (lt j k :: Γ) ⊢[PRAAx] lt j k := Prf.hyp0
    have r := natEq (binom_ratio h)
    have e0 := natEq (gle_of_le (le_of_lt h)); have e1 := natEq (gle_of_le h)
    apply deriveNat; ipra_simps
    linear_combination r + 𝔞(monus k j) * 𝔞(binom k j) * e0 - (𝔞 j + 1) * 𝔞(binom k (succ j)) * e1
  · have h : (le k j :: Γ) ⊢[PRAAx] monus k j ≐ zero := Prf.hyp0
    have g : (le k j :: Γ) ⊢[PRAAx] gb k (succ j) ≐ zero := gb_above ((succ_monus_succ _ _).eqTrans h)
    have e0 := natEq h; have e1 := natEq g
    apply deriveNat; ipra_simps
    linear_combination 𝔞(gle j k) * 𝔞(binom k j) * e0 - (𝔞 j + 1) * e1

/-- `(j + 1) C(k + 1, j + 1) + (k + 1) C(k, j + 1) = (k + 1) C(k + 1, j + 1)`. -/
theorem absorb_succ (k j : PTm n) :
    Γ ⊢[PRAAx] succ j * gb (succ k) (succ j) + succ k * gb k (succ j) ≐ succ k * gb (succ k) (succ j) := by
  refine .orE (lt_or_le k j) ?_ ?_
  · have z0 : (lt k j :: Γ) ⊢[PRAAx] gb k j ≐ zero := gb_above Prf.hyp0
    have z1 : (lt k j :: Γ) ⊢[PRAAx] gb k (succ j) ≐ zero :=
      gb_above (le_trans Prf.hyp0 (le_succ_self _))
    ipra_lc (𝔞 j - 𝔞 k) * natEq (gb_pascal (Γ := lt k j :: Γ) k j) + (𝔞 j - 𝔞 k) * natEq z0 + (𝔞 j + 1) * natEq z1
  · have p := natEq (gb_pascal (Γ := le j k :: Γ) k j)
    have r := natEq (gb_ratio (Γ := le j k :: Γ) k j)
    have e := natEq (eq_add_of_le (Prf.hyp0 : (le j k :: Γ) ⊢[PRAAx] le j k))
    apply deriveNat; ipra_simps
    linear_combination (𝔞 j - 𝔞 k) * p - r - 𝔞(gle j k) * 𝔞(binom k j) * e

/-- `i C(k + 1, i) + (k + 1) C(k, i) = (k + 1) C(k + 1, i)`. -/
theorem gb_absorb (k i : PTm n) :
    Γ ⊢[PRAAx] i * gb (succ k) i + succ k * gb k i ≐ succ k * gb (succ k) i := by
  refine .orE (zero_or_succ i) ?_ ?_
  · have hz : ((i ≐ zero) :: Γ) ⊢[PRAAx] i ≐ zero := Prf.hyp0
    have g1 : ((i ≐ zero) :: Γ) ⊢[PRAAx] gb (succ k) i ≐ gb (succ k) zero := congrGb (.eqRefl _) hz
    have g2 : ((i ≐ zero) :: Γ) ⊢[PRAAx] gb k i ≐ gb k zero := congrGb (.eqRefl _) hz
    refine (congrAdd (congrMul hz (.eqRefl _)) (congrMul (.eqRefl _) (g2.eqTrans (gb_zero k)))).eqTrans ?_
    refine .eqTrans ?_ (congrMul (.eqRefl _) (g1.eqTrans (gb_zero (succ k)))).eqSymm
    ipra_ring
  · have hs : ((i ≐ succ (pred i)) :: Γ) ⊢[PRAAx] i ≐ succ (pred i) := Prf.hyp0
    have g1 : ((i ≐ succ (pred i)) :: Γ) ⊢[PRAAx] gb (succ k) i ≐ gb (succ k) (succ (pred i)) := congrGb (.eqRefl _) hs
    have g2 : ((i ≐ succ (pred i)) :: Γ) ⊢[PRAAx] gb k i ≐ gb k (succ (pred i)) := congrGb (.eqRefl _) hs
    refine (congrAdd (congrMul hs g1) (congrMul (.eqRefl _) g2)).eqTrans ((absorb_succ k (pred i)).eqTrans ?_)
    exact (congrMul (.eqRefl _) g1).eqSymm

/-! ## The two parity sums -/

/-- `[K − i even] C(K, i) iᴺ`, over `0 = i`, `1 = ⟨N, K⟩`. -/
abbrev eB : PTm 2 := ev (monus (sndT (var 1)) (var 0)) * (gb (sndT (var 1)) (var 0) * pw (var 0) (fstT (var 1)))
/-- `[K − i odd] C(K, i) iᴺ`. -/
abbrev oB : PTm 2 := od (monus (sndT (var 1)) (var 0)) * (gb (sndT (var 1)) (var 0) * pw (var 0) (fstT (var 1)))

/-- `E⁺(N, K) = ∑_{i ≤ K} [K − i even] C(K, i) iᴺ`. -/
abbrev Ep (N K : PTm n) : PTm n := ap2 (sumF eB) (succ K) (pairT N K)
/-- `E⁻(N, K) = ∑_{i ≤ K} [K − i odd] C(K, i) iᴺ`. -/
abbrev Om (N K : PTm n) : PTm n := ap2 (sumF oB) (succ K) (pairT N K)

theorem eB_at (i N K : PTm n) :
    Γ ⊢[PRAAx] inst2 eB i (pairT N K) ≐ ev (monus K i) * (gb K i * pw i N) := by
  have e : inst2 eB i (pairT N K) = ev (monus (sndT (pairT N K)) i) * (gb (sndT (pairT N K)) i * pw i (fstT (pairT N K))) := by
    simp [inst2]
  rw [e]
  have s : Γ ⊢[PRAAx] sndT (pairT N K) ≐ K := snd_pair _ _
  exact congrMul (congrEv (congrMonus s (.eqRefl _))) (congrMul (congrGb s (.eqRefl _)) (congrAp2 powF (fst_pair _ _) (.eqRefl _)))

theorem oB_at (i N K : PTm n) :
    Γ ⊢[PRAAx] inst2 oB i (pairT N K) ≐ od (monus K i) * (gb K i * pw i N) := by
  have e : inst2 oB i (pairT N K) = od (monus (sndT (pairT N K)) i) * (gb (sndT (pairT N K)) i * pw i (fstT (pairT N K))) := by
    simp [inst2]
  rw [e]
  have s : Γ ⊢[PRAAx] sndT (pairT N K) ≐ K := snd_pair _ _
  exact congrMul (congrOd (congrMonus s (.eqRefl _))) (congrMul (congrGb s (.eqRefl _)) (congrAp2 powF (fst_pair _ _) (.eqRefl _)))

alias monus_succ_le := Common.monus_succ_of_le

/-- The pointwise step for the even part. -/
theorem step_e (N k i : PTm n) :
    Γ ⊢[PRAAx] inst2 eB i (pairT (succ N) (succ k)) + succ k * inst2 oB i (pairT N k) ≐
      succ k * inst2 eB i (pairT N (succ k)) := by
  refine (congrAdd (eB_at _ _ _) (congrMul (.eqRefl _) (oB_at _ _ _))).eqTrans (.eqTrans ?_
    (congrMul (.eqRefl _) (eB_at _ _ _)).eqSymm)
  have A := natEq (gb_absorb (Γ := Γ) k i)
  have ps := natEq (pw_succ (Γ := Γ) i N)
  refine .orE (lt_or_le k i) ?_ ?_
  · have z := natEq (gb_above (Prf.hyp0 : (lt k i :: Γ) ⊢[PRAAx] lt k i))
    have A' := natEq (gb_absorb (Γ := lt k i :: Γ) k i)
    have ps' := natEq (pw_succ (Γ := lt k i :: Γ) i N)
    apply deriveNat; ipra_simps
    linear_combination 𝔞(ev (monus (succ k) i)) * (𝔞(gle i (succ k)) * 𝔞(binom (succ k) i)) * ps' + 𝔞(ev (monus (succ k) i)) * 𝔞(pw i N) * A' + (𝔞 k + 1) * 𝔞(pw i N) * (𝔞(od (monus k i)) - 𝔞(ev (monus (succ k) i))) * z
  · have m := monus_succ_le (Prf.hyp0 : (le i k :: Γ) ⊢[PRAAx] le i k)
    have sw := natEq ((congrEv m).eqTrans (ev_succ _))
    have A' := natEq (gb_absorb (Γ := le i k :: Γ) k i)
    have ps' := natEq (pw_succ (Γ := le i k :: Γ) i N)
    apply deriveNat; ipra_simps
    linear_combination 𝔞(ev (monus (succ k) i)) * (𝔞(gle i (succ k)) * 𝔞(binom (succ k) i)) * ps' + 𝔞(ev (monus (succ k) i)) * 𝔞(pw i N) * A' - (𝔞 k + 1) * 𝔞(pw i N) * (𝔞(gle i k) * 𝔞(binom k i)) * sw

/-- The pointwise step for the odd part. -/
theorem step_o (N k i : PTm n) :
    Γ ⊢[PRAAx] inst2 oB i (pairT (succ N) (succ k)) + succ k * inst2 eB i (pairT N k) ≐
      succ k * inst2 oB i (pairT N (succ k)) := by
  refine (congrAdd (oB_at _ _ _) (congrMul (.eqRefl _) (eB_at _ _ _))).eqTrans (.eqTrans ?_
    (congrMul (.eqRefl _) (oB_at _ _ _)).eqSymm)
  refine .orE (lt_or_le k i) ?_ ?_
  · have z := natEq (gb_above (Prf.hyp0 : (lt k i :: Γ) ⊢[PRAAx] lt k i))
    have A' := natEq (gb_absorb (Γ := lt k i :: Γ) k i)
    have ps' := natEq (pw_succ (Γ := lt k i :: Γ) i N)
    apply deriveNat; ipra_simps
    linear_combination 𝔞(od (monus (succ k) i)) * (𝔞(gle i (succ k)) * 𝔞(binom (succ k) i)) * ps' +
      𝔞(od (monus (succ k) i)) * 𝔞(pw i N) * A' + (𝔞 k + 1) * 𝔞(pw i N) * (𝔞(ev (monus k i)) - 𝔞(od (monus (succ k) i))) * z
  · have m := monus_succ_le (Prf.hyp0 : (le i k :: Γ) ⊢[PRAAx] le i k)
    have sw := natEq ((congrOd m).eqTrans (od_succ _))
    have A' := natEq (gb_absorb (Γ := le i k :: Γ) k i)
    have ps' := natEq (pw_succ (Γ := le i k :: Γ) i N)
    apply deriveNat; ipra_simps
    linear_combination 𝔞(od (monus (succ k) i)) * (𝔞(gle i (succ k)) * 𝔞(binom (succ k) i)) * ps' +
      𝔞(od (monus (succ k) i)) * 𝔞(pw i N) * A' - (𝔞 k + 1) * 𝔞(pw i N) * (𝔞(gle i k) * 𝔞(binom k i)) * sw

/-! ## Combining sums with different parameters -/

def LB (f : PTm 2) : PTm 2 := Syn.subst ![var 0, fstT (var 1)] f
def RB (f : PTm 2) : PTm 2 := Syn.subst ![var 0, sndT (var 1)] f

theorem LB_at (f : PTm 2) (i a b : PTm n) : Γ ⊢[PRAAx] inst2 (LB f) i (pairT a b) ≐ inst2 f i a := by
  have e : inst2 (LB f) i (pairT a b) = inst2 f i (fstT (pairT a b)) := by
    simp only [inst2, LB, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  rw [e]; exact congrInst2 f (.eqRefl _) (fst_pair _ _)

theorem RB_at (f : PTm 2) (i a b : PTm n) : Γ ⊢[PRAAx] inst2 (RB f) i (pairT a b) ≐ inst2 f i b := by
  have e : inst2 (RB f) i (pairT a b) = inst2 f i (sndT (pairT a b)) := by
    simp only [inst2, RB, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
  rw [e]; exact congrInst2 f (.eqRefl _) (snd_pair _ _)

/-- `∑ f(x) + K ∑ g(y) = K ∑ h(z)` from the pointwise identity. -/
theorem sum_affine (f g h : PTm 2) {M K x y z : PTm n}
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶ (inst2 f (var 0) (Syn.shift x) +
      Syn.shift K * inst2 g (var 0) (Syn.shift y) ≐ Syn.shift K * inst2 h (var 0) (Syn.shift z)))) :
    Γ ⊢[PRAAx] ap2 (sumF f) M x + K * ap2 (sumF g) M y ≐ K * ap2 (sumF h) M z := by
  have c1 : Γ ⊢[PRAAx] ap2 (sumF f) M x + K * ap2 (sumF g) M y ≐
      ap2 (sumF (addBody (LB f) (RB (Probability.Lotus.cmB g)))) M (pairT x (pairT K y)) := by
    refine .eqTrans ?_ (sum_add _ _ _ _).eqSymm
    refine congrAdd (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))).eqSymm
      ((Probability.Lotus.sum_const_mul g M K y).eqSymm.eqTrans (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))).eqSymm)
    · simp only [shift_pairT]; exact LB_at f _ _ _
    · simp only [shift_pairT]; exact RB_at _ _ _ _
  refine c1.eqTrans ((sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))).eqTrans (Probability.Lotus.sum_const_mul h M K z))
  simp only [shift_pairT]
  rw [inst2_addBody]
  refine (congrAdd (LB_at f _ _ _) ((RB_at _ _ _ _).eqTrans (Probability.Independence.cm_pt g _ _ _))).eqTrans ?_
  exact (Prf.impE hp.allOpen.wk Prf.hyp0).eqTrans (Probability.Independence.cm_pt h _ _ _).eqSymm

/-- The odd sum at `K` read with one more (zero) term. -/
theorem Om_ext (N k : PTm n) : Γ ⊢[PRAAx] ap2 (sumF oB) (succ (succ k)) (pairT N k) ≐ Om N k := by
  refine (sum_succ' _ _ _).eqTrans ((congrAdd (.eqRefl _) ?_).eqTrans (add_zero _))
  refine (oB_at _ _ _).eqTrans ?_
  ipra_lc 𝔞(od (monus k (succ k))) * 𝔞(pw (succ k) N) * natEq (gb_above (Γ := Γ) (le_refl (succ k)))

theorem Ep_ext (N k : PTm n) : Γ ⊢[PRAAx] ap2 (sumF eB) (succ (succ k)) (pairT N k) ≐ Ep N k := by
  refine (sum_succ' _ _ _).eqTrans ((congrAdd (.eqRefl _) ?_).eqTrans (add_zero _))
  refine (eB_at _ _ _).eqTrans ?_
  ipra_lc 𝔞(ev (monus k (succ k))) * 𝔞(pw (succ k) N) * natEq (gb_above (Γ := Γ) (le_refl (succ k)))

/-- `E⁺(N + 1, k + 1) + (k + 1) E⁻(N, k) = (k + 1) E⁺(N, k + 1)`. -/
theorem Ep_step (N k : PTm n) : Γ ⊢[PRAAx] Ep (succ N) (succ k) + succ k * Om N k ≐ succ k * Ep N (succ k) := by
  refine (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (Om_ext N k).eqSymm)).eqTrans (sum_affine eB oB eB (.allI (.impI ?_)))
  simp only [shift_pairT]
  rw [show Syn.shift (succ N) = succ (Syn.shift N) by simp [Syn.shift], show Syn.shift (succ k) = succ (Syn.shift k) by simp [Syn.shift]]
  exact step_e _ _ _

/-- `E⁻(N + 1, k + 1) + (k + 1) E⁺(N, k) = (k + 1) E⁻(N, k + 1)`. -/
theorem Om_step (N k : PTm n) : Γ ⊢[PRAAx] Om (succ N) (succ k) + succ k * Ep N k ≐ succ k * Om N (succ k) := by
  refine (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (Ep_ext N k).eqSymm)).eqTrans (sum_affine oB eB oB (.allI (.impI ?_)))
  simp only [shift_pairT]
  rw [show Syn.shift (succ N) = succ (Syn.shift N) by simp [Syn.shift], show Syn.shift (succ k) = succ (Syn.shift k) by simp [Syn.shift]]
  exact step_o _ _ _

/-! ## The alternating binomial sum -/

/-- `[K − i even] C(K, i + 1)`, over `0 = i`, `1 = ⟨N, K⟩`. -/
abbrev xeB : PTm 2 := ev (monus (sndT (var 1)) (var 0)) * gb (sndT (var 1)) (succ (var 0))
/-- `[K − i odd] C(K, i + 1)`. -/
abbrev xoB : PTm 2 := od (monus (sndT (var 1)) (var 0)) * gb (sndT (var 1)) (succ (var 0))

theorem xeB_at (i N K : PTm n) : Γ ⊢[PRAAx] inst2 xeB i (pairT N K) ≐ ev (monus K i) * gb K (succ i) := by
  have e : inst2 xeB i (pairT N K) = ev (monus (sndT (pairT N K)) i) * gb (sndT (pairT N K)) (succ i) := by simp [inst2]
  rw [e]
  have s : Γ ⊢[PRAAx] sndT (pairT N K) ≐ K := snd_pair _ _
  exact congrMul (congrEv (congrMonus s (.eqRefl _))) (congrGb s (.eqRefl _))

theorem xoB_at (i N K : PTm n) : Γ ⊢[PRAAx] inst2 xoB i (pairT N K) ≐ od (monus K i) * gb K (succ i) := by
  have e : inst2 xoB i (pairT N K) = od (monus (sndT (pairT N K)) i) * gb (sndT (pairT N K)) (succ i) := by simp [inst2]
  rw [e]
  have s : Γ ⊢[PRAAx] sndT (pairT N K) ≐ K := snd_pair _ _
  exact congrMul (congrOd (congrMonus s (.eqRefl _))) (congrGb s (.eqRefl _))

theorem pw_zero' (i : PTm n) : Γ ⊢[PRAAx] pw i zero ≐ one := pw_zero i

/-- Shifting the even sum at `k + 1`: `[k + 1 − (i + 1) even] C(k + 1, i + 1) = [k − i even] (C(k, i) + C(k, i + 1))`. -/
theorem shift_e (i k : PTm n) :
    Γ ⊢[PRAAx] inst2 (shiftBody eB) i (pairT zero (succ k)) ≐ inst2 (addBody eB xeB) i (pairT zero k) := by
  rw [inst2_shiftBody, inst2_addBody]
  refine (eB_at _ _ _).eqTrans (.eqTrans ?_ (congrAdd (eB_at _ _ _) (xeB_at _ _ _)).eqSymm)
  ipra_lc (𝔞(gle (succ i) (succ k)) * 𝔞(binom (succ k) (succ i))) * 𝔞(pw (succ i) zero) * natEq (congrEv (succ_monus_succ (Γ := Γ) k i)) +
    𝔞(ev (monus k i)) * 𝔞(pw (succ i) zero) * natEq (gb_pascal (Γ := Γ) k i) +
    𝔞(ev (monus k i)) * (𝔞(gle (succ i) k) * 𝔞(binom k (succ i))) * natEq (pw_zero' (Γ := Γ) (succ i)) +
    𝔞(ev (monus k i)) * (𝔞(gle i k) * 𝔞(binom k i)) * (natEq (pw_zero' (Γ := Γ) (succ i)) - natEq (pw_zero' (Γ := Γ) i))

theorem shift_o (i k : PTm n) :
    Γ ⊢[PRAAx] inst2 (shiftBody oB) i (pairT zero (succ k)) ≐ inst2 (addBody oB xoB) i (pairT zero k) := by
  rw [inst2_shiftBody, inst2_addBody]
  refine (oB_at _ _ _).eqTrans (.eqTrans ?_ (congrAdd (oB_at _ _ _) (xoB_at _ _ _)).eqSymm)
  ipra_lc (𝔞(gle (succ i) (succ k)) * 𝔞(binom (succ k) (succ i))) * 𝔞(pw (succ i) zero) * natEq (congrOd (succ_monus_succ (Γ := Γ) k i)) +
    𝔞(od (monus k i)) * 𝔞(pw (succ i) zero) * natEq (gb_pascal (Γ := Γ) k i) +
    𝔞(od (monus k i)) * (𝔞(gle (succ i) k) * 𝔞(binom k (succ i))) * natEq (pw_zero' (Γ := Γ) (succ i)) +
    𝔞(od (monus k i)) * (𝔞(gle i k) * 𝔞(binom k i)) * (natEq (pw_zero' (Γ := Γ) (succ i)) - natEq (pw_zero' (Γ := Γ) i))

alias mul_one' := Common.mul_one_right

theorem shift_pairT0 (k : PTm n) : Syn.shift (pairT zero k) = pairT zero (Syn.shift k) := by simp [Syn.shift]

/-- `k ∸ i = (k ∸ (i + 1)) + 1` for `i < k`. -/
alias monus_lt := Common.monus_succ_of_lt

theorem head_e (K : PTm n) : Γ ⊢[PRAAx] inst2 eB zero (pairT zero K) ≐ ev K :=
  (eB_at _ _ _).eqTrans ((congrMul (congrEv (monus_zero K)) ((congrMul (gb_zero K) (pw_zero' _)).eqTrans (one_mul _))).eqTrans
    (mul_one' _))

theorem head_o (K : PTm n) : Γ ⊢[PRAAx] inst2 oB zero (pairT zero K) ≐ od K :=
  (oB_at _ _ _).eqTrans ((congrMul (congrOd (monus_zero K)) ((congrMul (gb_zero K) (pw_zero' _)).eqTrans (one_mul _))).eqTrans
    (mul_one' _))

/-- The last extra term vanishes: `∑_{i<k+1} x(i) = ∑_{i<k} x(i)` for the shifted bodies. -/
theorem xe_ext (k : PTm n) : Γ ⊢[PRAAx] ap2 (sumF xeB) (succ k) (pairT zero k) ≐ ap2 (sumF xeB) k (pairT zero k) := by
  refine (sum_succ' _ _ _).eqTrans ((congrAdd (.eqRefl _) ((xeB_at _ _ _).eqTrans ?_)).eqTrans (add_zero _))
  exact (congrMul (.eqRefl _) (gb_above (le_refl _))).eqTrans (mul_zero _)

theorem xo_ext (k : PTm n) : Γ ⊢[PRAAx] ap2 (sumF xoB) (succ k) (pairT zero k) ≐ ap2 (sumF xoB) k (pairT zero k) := by
  refine (sum_succ' _ _ _).eqTrans ((congrAdd (.eqRefl _) ((xoB_at _ _ _).eqTrans ?_)).eqTrans (add_zero _))
  exact (congrMul (.eqRefl _) (gb_above (le_refl _))).eqTrans (mul_zero _)

/-- `E⁺(0, k) = [k even] + ∑_{i<k} [k − i odd] C(k, i + 1)`. -/
theorem Ep0_split (k : PTm n) : Γ ⊢[PRAAx] Ep zero k ≐ ev k + ap2 (sumF xoB) k (pairT zero k) := by
  refine (sum_shift eB k (pairT zero k)).eqTrans (congrAdd (head_e k) (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))))
  rw [shift_pairT0, inst2_shiftBody]
  refine (eB_at _ _ _).eqTrans (.eqTrans ?_ (xoB_at _ _ _).eqSymm)
  have m := monus_lt (Prf.hyp0 : (lt (var 0) (Syn.shift k) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift k))
  have sw := (congrOd m).eqTrans (od_succ _)
  exact congrMul sw.eqSymm ((congrMul (.eqRefl _) (pw_zero' _)).eqTrans (mul_one' _))

/-- `E⁻(0, k) = [k odd] + ∑_{i<k} [k − i even] C(k, i + 1)`. -/
theorem Om0_split (k : PTm n) : Γ ⊢[PRAAx] Om zero k ≐ od k + ap2 (sumF xeB) k (pairT zero k) := by
  refine (sum_shift oB k (pairT zero k)).eqTrans (congrAdd (head_o k) (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))))
  rw [shift_pairT0, inst2_shiftBody]
  refine (oB_at _ _ _).eqTrans (.eqTrans ?_ (xeB_at _ _ _).eqSymm)
  have m := monus_lt (Prf.hyp0 : (lt (var 0) (Syn.shift k) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift k))
  have sw := (congrEv m).eqTrans (ev_succ _)
  exact congrMul sw.eqSymm ((congrMul (.eqRefl _) (pw_zero' _)).eqTrans (mul_one' _))

/-- `E⁺(0, k + 1) = E⁻(0, k) + E⁺(0, k)`. -/
theorem alt_e (k : PTm n) : Γ ⊢[PRAAx] Ep zero (succ k) ≐ Om zero k + Ep zero k := by
  refine (sum_shift eB (succ k) (pairT zero (succ k))).eqTrans ?_
  have hs : Γ ⊢[PRAAx] ap2 (sumF (shiftBody eB)) (succ k) (pairT zero (succ k)) ≐
      ap2 (sumF (addBody eB xeB)) (succ k) (pairT zero k) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT0, shift_pairT0, show Syn.shift (succ k) = succ (Syn.shift k) by simp [Syn.shift]]
    exact shift_e _ _
  ipra_lc natEq (head_e (Γ := Γ) (succ k)) + natEq hs + natEq (sum_add (Γ := Γ) eB xeB (succ k) (pairT zero k)) -
    natEq (Om0_split (Γ := Γ) k) + natEq (xe_ext (Γ := Γ) k) + natEq (ev_succ (Γ := Γ) k)

/-- `E⁻(0, k + 1) = E⁺(0, k) + E⁻(0, k)`. -/
theorem alt_o (k : PTm n) : Γ ⊢[PRAAx] Om zero (succ k) ≐ Ep zero k + Om zero k := by
  refine (sum_shift oB (succ k) (pairT zero (succ k))).eqTrans ?_
  have hs : Γ ⊢[PRAAx] ap2 (sumF (shiftBody oB)) (succ k) (pairT zero (succ k)) ≐
      ap2 (sumF (addBody oB xoB)) (succ k) (pairT zero k) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT0, shift_pairT0, show Syn.shift (succ k) = succ (Syn.shift k) by simp [Syn.shift]]
    exact shift_o _ _
  ipra_lc natEq (head_o (Γ := Γ) (succ k)) + natEq hs + natEq (sum_add (Γ := Γ) oB xoB (succ k) (pairT zero k)) -
    natEq (Ep0_split (Γ := Γ) k) + natEq (xo_ext (Γ := Γ) k) + natEq (od_succ (Γ := Γ) k)

/-! ## The inclusion–exclusion identity -/

/-- The claim `k! S(N, k) + E⁻(N, k) = E⁺(N, k)`. -/
abbrev P (N K : PTm n) : Fm PTm n := fact K * stir N K + Om N K ≐ Ep N K

theorem congrP {N K K' : PTm n} (hk : Γ ⊢[PRAAx] K ≐ K') (h : Γ ⊢[PRAAx] P N K') : Γ ⊢[PRAAx] P N K := by
  have cf : Γ ⊢[PRAAx] fact K ≐ fact K' := congrAp2 factF hk (.eqRefl _)
  have cs : Γ ⊢[PRAAx] stir N K ≐ stir N K' := StirlingPowers.congrStir (.eqRefl _) hk
  have co : Γ ⊢[PRAAx] Om N K ≐ Om N K' := congrAp2 _ (congrSucc hk) (congrPairT (.eqRefl _) hk)
  have ce : Γ ⊢[PRAAx] Ep N K ≐ Ep N K' := congrAp2 _ (congrSucc hk) (congrPairT (.eqRefl _) hk)
  exact (congrAdd (congrMul cf cs) co).eqTrans (h.eqTrans ce.eqSymm)

theorem sum1 (f : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF f) (succ zero) x ≐ inst2 f zero x :=
  (sum_succ' f zero x).eqTrans ((congrAdd (sum_zero f x) (.eqRefl _)).eqTrans (zero_add _))

theorem base0 : Γ ⊢[PRAAx] P (zero : PTm n) zero := by
  ipra_lc 𝔞(gle (zero : PTm n) zero) * 𝔞(Bell.nth (Stirling.row (zero : PTm n)) (monus zero zero)) * natEq (fact_zero (Γ := Γ) (zero : PTm n)) +
    natEq (Stirling.stir_zero (Γ := Γ) (n := n)) +
    natEq ((sum1 oB _).eqTrans ((head_o (Γ := Γ) (zero : PTm n)).eqTrans (par_zero (Γ := Γ)))) -
    natEq ((sum1 eB _).eqTrans ((head_e (Γ := Γ) (zero : PTm n)).eqTrans ev_zero))

theorem base_succ (k : PTm n) : Γ ⊢[PRAAx] P zero (succ k) := by
  have z : Γ ⊢[PRAAx] stir zero (succ k) ≐ zero := Stirling.stir_above ((succ_monus_succ _ _).eqTrans (zero_le k))
  ipra_lc 𝔞(fact (succ k)) * natEq z + natEq (alt_o (Γ := Γ) k) - natEq (alt_e (Γ := Γ) k)

/-- `n = 0`: `k! S(0, k) + E⁻(0, k) = E⁺(0, k)`, the alternating binomial sum. -/
theorem base (K : PTm n) : Γ ⊢[PRAAx] P zero K := by
  refine .orE (zero_or_succ K) ?_ ?_
  · exact congrP Prf.hyp0 base0
  · exact congrP Prf.hyp0 (base_succ _)

theorem pt_zero (N : PTm n) : Γ ⊢[PRAAx] P (succ N) zero := by
  ipra_lc 𝔞(fact (zero : PTm n)) * natEq (Stirling.stir_succ_zero (Γ := Γ) N) +
    natEq ((sum1 oB _).eqTrans (oB_at (Γ := Γ) zero (succ N) zero)) -
    natEq ((sum1 eB _).eqTrans (eB_at (Γ := Γ) zero (succ N) zero)) +
    (𝔞(od (monus (zero : PTm n) zero)) - 𝔞(ev (monus (zero : PTm n) zero))) * (𝔞(gle (zero : PTm n) zero) * 𝔞(binom (zero : PTm n) zero)) * natEq ((pw_succ (Γ := Γ) zero N).eqTrans (mul_zero _))

theorem pt_succ {N k : PTm n} (h1 : Γ ⊢[PRAAx] P N (succ k)) (h0 : Γ ⊢[PRAAx] P N k) :
    Γ ⊢[PRAAx] P (succ N) (succ k) := by
  ipra_lc 𝔞(ap2 factF (succ k) zero) * natEq (StirlingBinomial.stir_rec (Γ := Γ) N k) + natEq (Om_step (Γ := Γ) N k) -
    natEq (Ep_step (Γ := Γ) N k) + (𝔞 k + 1) * natEq h1 + (𝔞 k + 1) * natEq h0 +
    𝔞(gle k N) * 𝔞(Bell.nth (Stirling.row N) (monus N k)) * natEq (fact_succ (Γ := Γ) k zero)

/-- The violation body `1 ∸ [k! S(N, k) + E⁻ = E⁺]`, over `0 = k`, `1 = N`. -/
abbrev vB : PTm 2 :=
  monus one (eqb (fact (var 0) * stir (var 1) (var 0) + ap2 (sumF oB) (succ (var 0)) (pairT (var 1) (var 0)))
    (ap2 (sumF eB) (succ (var 0)) (pairT (var 1) (var 0))))

theorem vB_at (k N : PTm n) : inst2 vB k N = monus one (eqb (fact k * stir N k + Om N k) (Ep N k)) := by
  simp [inst2]

theorem elim {B N k : PTm n} (hV : Γ ⊢[PRAAx] ap2 (sumF vB) B N ≐ zero) (hk : Γ ⊢[PRAAx] lt k B) : Γ ⊢[PRAAx] P N k := by
  have h := sum_zero_elim _ hV hk
  rw [vB_at] at h
  exact AnalyticNumberTheory.EulerProduct.eq_of_viol h

theorem V_zero (B : PTm n) : Γ ⊢[PRAAx] ap2 (sumF vB) B zero ≐ zero := by
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  rw [show Syn.shift (zero : PTm n) = zero by simp [Syn.shift], vB_at]
  exact AnalyticNumberTheory.EulerProduct.viol_of_eq (base _)

theorem V_succ {B N : PTm n} (hV : Γ ⊢[PRAAx] ap2 (sumF vB) B N ≐ zero) : Γ ⊢[PRAAx] ap2 (sumF vB) B (succ N) ≐ zero := by
  have hV' : Γ.map Fm.shift ⊢[PRAAx] ap2 (sumF vB) (Syn.shift B) (Syn.shift N) ≐ zero := by
    have e := hV.shift
    simp only [Fm.shift, Fm.subst_eq, subst_ap2, ConciseIPRA.PTm.subst_zero] at e
    exact e
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  rw [show Syn.shift (succ N) = succ (Syn.shift N) by simp [Syn.shift], vB_at]
  refine AnalyticNumberTheory.EulerProduct.viol_of_eq ?_
  refine .orE (zero_or_succ (var 0)) ?_ ?_
  · exact congrP Prf.hyp0 (pt_zero _)
  · let C := ((var 0 : PTm (n + 1)) ≐ succ (pred (var 0))) :: lt (var 0) (Syn.shift B) :: Γ.map Fm.shift
    have z : C ⊢[PRAAx] (var 0 : PTm (n + 1)) ≐ succ (pred (var 0)) := Prf.hyp0
    have hk : C ⊢[PRAAx] lt (var 0) (Syn.shift B) := Prf.hyp1
    have hk' : C ⊢[PRAAx] lt (pred (var 0)) (Syn.shift B) :=
      lt_of_lt_of_le (le_congr (.eqRefl _) z.eqSymm (le_refl _)) (le_of_lt hk)
    have h1 : C ⊢[PRAAx] P (Syn.shift N) (succ (pred (var 0))) := congrP z.eqSymm (elim hV'.wk.wk hk)
    exact congrP z (pt_succ h1 (elim hV'.wk.wk hk'))

/-- `eq:stirling-ie`: `k! S(n, k) + ∑_{i≤k} [k − i odd] C(k, i) iⁿ = ∑_{i≤k} [k − i even] C(k, i) iⁿ`, i.e.
`k! S(n, k) = ∑_{i≤k} (−1)^{k−i} C(k, i) iⁿ`, for all `n, k`. -/
theorem stirling_ie (N K : PTm n) : Γ ⊢[PRAAx] P N K := by
  have hall : Γ ⊢[PRAAx] Fm.all (ap2 (sumF vB) (Syn.shift (succ K)) (var 0) ≐ zero) := by
    ipra_qfind [subst_ap2]
    · exact V_zero _
    · exact V_succ Prf.hyp0
  have h := Prf.allE N hall
  simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h
  exact elim h (le_refl _)

/-! ## The Bell number as a sum of exact quotients (`eq:bell-ie`) -/

/-- `(E⁺(n, k) ∸ E⁻(n, k)) / k!`, over `0 = k`, `1 = n`. -/
abbrev qB : PTm 2 := quo (monus (ap2 (sumF eB) (succ (var 0)) (pairT (var 1) (var 0)))
  (ap2 (sumF oB) (succ (var 0)) (pairT (var 1) (var 0)))) (fact (var 0))

/-- The signed sum is exactly divisible by `k!`, with quotient `S(n, k)`. -/
theorem q_eq (N K : PTm n) : Γ ⊢[PRAAx] quo (monus (Ep N K) (Om N K)) (fact K) ≐ stir N K := by
  have d : Γ ⊢[PRAAx] monus (Ep N K) (Om N K) ≐ fact K * stir N K :=
    (congrMonus (stirling_ie N K).eqSymm (.eqRefl _)).eqTrans (add_monus _ _)
  have hf := AnalyticNumberTheory.Primes.fact_pos (Γ := Γ) K
  have hl : Γ ⊢[PRAAx] lt zero (fact K) :=
    le_of_eq_add (d := pred (fact K)) (by have e := natEq hf; apply deriveNat; ipra_simps; linear_combination e)
  exact (congrAp2 quoF d (.eqRefl _)).eqTrans
    (AnalyticNumberTheory.Totient.quo_eq hf (r := zero) (by ipra_ring) hl)

/-- `eq:bell-ie`: `B_n = ∑_{k ≤ n} (1/k!) ∑_{i ≤ k} (−1)^{k−i} C(k, i) iⁿ`, each summand an exact quotient. -/
theorem bell_ie (N : PTm n) : Γ ⊢[PRAAx] ap2 (sumF qB) (succ N) N ≐ Bell.bell N := by
  refine .eqTrans ?_ (BellStirling.bell_stirling N)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  have e : inst2 qB (var 0) (Syn.shift N) = quo (monus (Ep (Syn.shift N) (var 0)) (Om (Syn.shift N) (var 0))) (fact (var 0)) := by
    simp [inst2]
  have e' : inst2 BellStirling.tB (var 0) (Syn.shift N) = stir (Syn.shift N) (var 0) := by simp [inst2]
  rw [e, e']
  exact q_eq _ _

end LeanProofs.IPRA.Combinatorics.StirlingInclusion
