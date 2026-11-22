import IPRADerivations.AnalyticNumberTheory.GramCertificate
import IPRADerivations.Foundations.ErrorBudget
import IPRADerivations.Core.Gcd

/-!
# The rational Gram certificate

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/07_sw_bv.tex`, Proposition "Rational Gram
certificate": "Let `A` be an `R × N` matrix over `ℚ(i)` and let `K = A A*`. Suppose symmetric nonnegative rational
numbers `k_rs` and a rational `L ≥ 0` satisfy `|K_rs|² ≤ k_rs²`, `Σ_s k_rs ≤ L`. Then, for every `a ∈ ℚ(i)^N`,
`Σ_r |Σ_n A_rn a_n|² ≤ L Σ_n |a_n|²`."

Denominators are cleared: `A = X + iY` and `a = p + iq` have integer-term entries (`ZT`), the bounds `k_rs` and `L`
are natural terms, and the dimensions are fixed metalevel numbers. The proof follows the packet:

* `pair_free`: `|z|² ≤ k²` gives `2 Re(ū z v) ≤ k (|u|² + |v|²)` — `GramCertificate.pair_bound` divided by `k > 0`
  (`zle_cancel`), and for `k = 0` the hypothesis forces `z = 0` (`sq_sum_zero`);
* `adj_norm`, `adj_real`, `adj_imag`: `‖A*b‖² = Σ_{r,s} Re(b̄_r K_rs b_s)` and `⟨a, A*b⟩ = ⟨Aa, b⟩`;
* `sym_sum`: `Σ_{r,s} k_rs (|b_r|² + |b_s|²) = 2 Σ_r |b_r|² Σ_s k_rs` for symmetric `k`;
* `gram_ring`: the resulting certificate identity
  `2 ‖b‖² (L ‖a‖² − ‖b‖²) = ‖a‖² · [Σ pair slacks + 2 Σ_r |b_r|² (L − Σ_s k_rs)] + 2 · [Cauchy–Schwarz slack]` for `b = Aa`;
* `gram_bound`: `Σ_r |Σ_n A_rn a_n|² ≤ L Σ_n |a_n|²`, after cancelling `2 ‖b‖²` (a decidable zero test on a natural
  term, as in the packet: "If `‖b‖² = 0`, there is nothing to prove; otherwise divide").
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.GramBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Foundations.ErrorBudget (nsum toG_nsum)
open LeanProofs.IPRA.AnalyticNumberTheory.GramCertificate (gauss_cs pair_bound)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Order facts for integer terms -/

/-- `a² = 0 → a = 0` for natural terms. -/
theorem nat_self_zero {a : PTm n} (h : Γ ⊢[PRAAx] a * a ≐ zero) : Γ ⊢[PRAAx] a ≐ zero := by
  have l : Γ ⊢[PRAAx] le (a * a) (zero * zero) := le_congr h.eqSymm (zero_mul zero).eqSymm (le_refl zero)
  exact (monus_zero a).eqSymm.eqTrans (nat_sqrt_mono l)

/-- An integer term whose square is zero is zero. -/
theorem toZ_zero_of_sq {x : ZT n} (h : Γ ⊢[PRAAx] ad x.pos x.neg * ad x.pos x.neg ≐ zero) : ZT.toZ Γ x = 0 := by
  have a0 := nat_self_zero h
  have h1 : Γ ⊢[PRAAx] le x.pos x.neg := add_eq_zero_left a0
  have h2 : Γ ⊢[PRAAx] le x.neg x.pos := add_eq_zero_left ((add_comm _ _).eqTrans a0)
  have e := natEq (le_antisymm h1 h2)
  rw [toZ_def, e, sub_self]

/-- `x² + y² ≤ k²` with `k = 0` forces `x = y = 0`. -/
theorem sq_sum_zero {x y : ZT n} {k : PTm n} (hk : Γ ⊢[PRAAx] k ≐ zero)
    (h : Γ ⊢[PRAAx] zle (ZT.sq x + ZT.sq y) (ZT.ofNat (k * k))) : ZT.toZ Γ x = 0 ∧ ZT.toZ Γ y = 0 := by
  obtain ⟨w, hw⟩ := nn_zsl h
  have ex := sq_nat (Γ := Γ) x
  have ey := sq_nat (Γ := Γ) y
  have ek := natEq hk
  have hsum : Γ ⊢[PRAAx] (ad x.pos x.neg * ad x.pos x.neg + ad y.pos y.neg * ad y.pos y.neg) + w ≐ zero := by
    apply deriveNat
    rw [zsl_def, ZT.toZ_add, ex, ey, ZT.toZ_ofNat] at hw
    simp only [Q.mk_add, Q.mk_mul, Q.mk_zero, map_add, map_mul, map_zero] at hw ek ⊢
    linear_combination -hw + Groth.ι (Q.mk Γ k) * ek
  have hAB := add_eq_zero_left hsum
  exact ⟨toZ_zero_of_sq (add_eq_zero_left hAB), toZ_zero_of_sq (add_eq_zero_left ((add_comm _ _).eqTrans hAB))⟩

/-- Cancelling a positive natural factor in an integer inequality. -/
theorem zle_cancel {k : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) {u v : ZT n}
    (h : Γ ⊢[PRAAx] zle (ZT.ofNat k * u) (ZT.ofNat k * v)) : Γ ⊢[PRAAx] zle u v := by
  have h0 : Γ ⊢[PRAAx] le ((k * u.pos + zero * u.neg) + (k * v.neg + zero * v.pos))
      ((k * v.pos + zero * v.neg) + (k * u.neg + zero * u.pos)) := h
  have h' : Γ ⊢[PRAAx] le (k * (u.pos + v.neg)) (k * (v.pos + u.neg)) :=
    le_congr (by apply deriveNat; ipra_simps; ring) (by apply deriveNat; ipra_simps; ring) h0
  exact mul_le_cancel (le_congr (congrMul hk (.eqRefl _)) (congrMul hk (.eqRefl _)) h')

/-- `|z|² ≤ k²` gives `2 Re(ū z v) ≤ k (|u|² + |v|²)` for every natural `k`. -/
theorem pair_free {k : PTm n} {z₁ z₂ : ZT n} (u₁ u₂ v₁ v₂ : ZT n)
    (hz : Γ ⊢[PRAAx] zle (ZT.sq z₁ + ZT.sq z₂) (ZT.ofNat (k * k))) :
    Γ ⊢[PRAAx] zle (ZT.natLit 2 * (u₁ * (z₁ * v₁ - z₂ * v₂) + u₂ * (z₁ * v₂ + z₂ * v₁)))
      (ZT.ofNat k * (ZT.sq u₁ + ZT.sq u₂ + (ZT.sq v₁ + ZT.sq v₂))) := by
  refine .orE (zero_or_succ k) ?_ ?_
  · have hk : ((k ≐ zero) :: Γ) ⊢[PRAAx] k ≐ zero := Prf.hyp0
    obtain ⟨e1, e2⟩ := sq_sum_zero hk hz.wk
    have ek := natEq hk
    refine zle_of_comb 0 ?_ nn_zero
    simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_sq, ZT.toZ_natLit, ZT.toZ_ofNat, Q.mk_zero, map_zero] at ek ⊢
    rw [ek, e1, e2]
    ring
  · have hk : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] k ≐ succ (pred k) := Prf.hyp0
    have pb := pair_bound (Γ := (k ≐ succ (pred k)) :: Γ) u₁ u₂ v₁ v₂ hz.wk
    refine zle_cancel hk (zle_of_comb (zsl pb) ?_ (nn_zsl pb))
    simp only [zsl_def, ZT.toZ_mul, ZT.toZ_natLit, ZT.toZ_ofNat, Q.mk_mul, map_mul]
    ring

/-! ## Ring identities -/

section Ring

variable {R : Type*} [CommRing R] {ρ ν : ℕ}

/-- `‖A*b‖² = Σ_{r,s} Re(b̄_r K_rs b_s)` for `A = x + iy`, `b = b₁ + i b₂`, `K = A A*`. -/
theorem adj_norm (x y : Fin ρ → Fin ν → R) (b₁ b₂ : Fin ρ → R) :
    ∑ m, ((∑ r, (x r m * b₁ r + y r m * b₂ r)) ^ 2 + (∑ r, (x r m * b₂ r - y r m * b₁ r)) ^ 2) =
      ∑ r, ∑ s, (b₁ r * ((∑ m, (x r m * x s m + y r m * y s m)) * b₁ s -
            (∑ m, (y r m * x s m - x r m * y s m)) * b₂ s) +
          b₂ r * ((∑ m, (x r m * x s m + y r m * y s m)) * b₂ s +
            (∑ m, (y r m * x s m - x r m * y s m)) * b₁ s)) := by
  have hT : ∀ r s, (b₁ r * ((∑ m, (x r m * x s m + y r m * y s m)) * b₁ s -
        (∑ m, (y r m * x s m - x r m * y s m)) * b₂ s) +
      b₂ r * ((∑ m, (x r m * x s m + y r m * y s m)) * b₂ s +
        (∑ m, (y r m * x s m - x r m * y s m)) * b₁ s)) =
      ∑ m, ((x r m * b₁ r + y r m * b₂ r) * (x s m * b₁ s + y s m * b₂ s) +
        (x r m * b₂ r - y r m * b₁ r) * (x s m * b₂ s - y s m * b₁ s)) := by
    intro r s
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  calc ∑ m, ((∑ r, (x r m * b₁ r + y r m * b₂ r)) ^ 2 + (∑ r, (x r m * b₂ r - y r m * b₁ r)) ^ 2)
      = ∑ m, ∑ r, ∑ s, ((x r m * b₁ r + y r m * b₂ r) * (x s m * b₁ s + y s m * b₂ s) +
          (x r m * b₂ r - y r m * b₁ r) * (x s m * b₂ s - y s m * b₁ s)) :=
        Finset.sum_congr rfl fun m _ => by
          rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum]
          refine Finset.sum_add_distrib.symm.trans (Finset.sum_congr rfl fun r _ => ?_)
          exact Finset.sum_add_distrib.symm
    _ = ∑ r, ∑ m, ∑ s, ((x r m * b₁ r + y r m * b₂ r) * (x s m * b₁ s + y s m * b₂ s) +
          (x r m * b₂ r - y r m * b₁ r) * (x s m * b₂ s - y s m * b₁ s)) := Finset.sum_comm
    _ = ∑ r, ∑ s, ∑ m, ((x r m * b₁ r + y r m * b₂ r) * (x s m * b₁ s + y s m * b₂ s) +
          (x r m * b₂ r - y r m * b₁ r) * (x s m * b₂ s - y s m * b₁ s)) :=
        Finset.sum_congr rfl fun r _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => (hT r s).symm

/-- `Re ⟨a, A*b⟩ = Re ⟨Aa, b⟩`. -/
theorem adj_real (x y : Fin ρ → Fin ν → R) (p q : Fin ν → R) (b₁ b₂ : Fin ρ → R) :
    ∑ m, (p m * ∑ r, (x r m * b₁ r + y r m * b₂ r) + q m * ∑ r, (x r m * b₂ r - y r m * b₁ r)) =
      ∑ r, (b₁ r * ∑ m, (x r m * p m - y r m * q m) + b₂ r * ∑ m, (x r m * q m + y r m * p m)) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun m _ => by ring)

/-- `Im ⟨a, A*b⟩ = Im ⟨Aa, b⟩`. -/
theorem adj_imag (x y : Fin ρ → Fin ν → R) (p q : Fin ν → R) (b₁ b₂ : Fin ρ → R) :
    ∑ m, (p m * ∑ r, (x r m * b₂ r - y r m * b₁ r) - q m * ∑ r, (x r m * b₁ r + y r m * b₂ r)) =
      ∑ r, (b₂ r * ∑ m, (x r m * p m - y r m * q m) - b₁ r * ∑ m, (x r m * q m + y r m * p m)) := by
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun m _ => by ring)

/-- For symmetric `κ`: `Σ_{r,s} (κ_rs (B_r + B_s) − 2 T_rs) + 2 Σ_r B_r (L − Σ_s κ_rs) = 2 (L Σ B − Σ T)`. -/
theorem sym_sum (κ : Fin ρ → Fin ρ → R) (B : Fin ρ → R) (T : Fin ρ → Fin ρ → R) (Lg : R)
    (hs : ∀ r s, κ r s = κ s r) :
    ∑ r, ∑ s, (κ r s * (B r + B s) - 2 * T r s) + 2 * ∑ r, B r * (Lg - ∑ s, κ r s) =
      2 * (Lg * ∑ r, B r - ∑ r, ∑ s, T r s) := by
  have h1 : ∑ r, ∑ s, κ r s * B s = ∑ r, B r * ∑ s, κ r s := by
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun s _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [hs r s]; ring
  have h2 : ∑ r, ∑ s, κ r s * B r = ∑ r, B r * ∑ s, κ r s :=
    Finset.sum_congr rfl fun r _ => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  have e : ∀ r s, κ r s * (B r + B s) - 2 * T r s = κ r s * B r + κ r s * B s - 2 * T r s := fun r s => by ring
  have s1 : ∑ r, ∑ s, (κ r s * (B r + B s) - 2 * T r s) =
      (∑ r, ∑ s, κ r s * B r) + (∑ r, ∑ s, κ r s * B s) - 2 * ∑ r, ∑ s, T r s := by
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have s2 : ∑ r, B r * (Lg - ∑ s, κ r s) = Lg * ∑ r, B r - ∑ r, B r * ∑ s, κ r s := by
    have e2 : ∀ r, B r * (Lg - ∑ s, κ r s) = Lg * B r - B r * ∑ s, κ r s := fun r => by ring
    simp only [e2, Finset.sum_sub_distrib, ← Finset.mul_sum]
  linear_combination s1 + 2 * s2 + h2 + h1

theorem master_alg (Bt Pa Lg S Cn TT Rr Ii : R) (hsym : S = 2 * (Lg * Bt - TT)) (hn : Cn = TT) (hr : Rr = Bt)
    (hi : Ii = 0) : Pa * S + 2 * (Pa * Cn - (Rr ^ 2 + Ii ^ 2)) = 2 * Bt * (Lg * Pa - Bt) := by
  subst hn hr hi hsym; ring

/-- The certificate identity of the Gram bound for `b = A a`. -/
theorem gram_ring (x y : Fin ρ → Fin ν → R) (p q : Fin ν → R) (β₁ β₂ : Fin ρ → R) (K₁ K₂ : Fin ρ → Fin ρ → R)
    (c₁ c₂ : Fin ν → R) (κ : Fin ρ → Fin ρ → R) (Lg : R)
    (hb₁ : ∀ r, β₁ r = ∑ m, (x r m * p m - y r m * q m)) (hb₂ : ∀ r, β₂ r = ∑ m, (x r m * q m + y r m * p m))
    (hK₁ : ∀ r s, K₁ r s = ∑ m, (x r m * x s m + y r m * y s m))
    (hK₂ : ∀ r s, K₂ r s = ∑ m, (y r m * x s m - x r m * y s m))
    (hc₁ : ∀ m, c₁ m = ∑ r, (x r m * β₁ r + y r m * β₂ r)) (hc₂ : ∀ m, c₂ m = ∑ r, (x r m * β₂ r - y r m * β₁ r))
    (hs : ∀ r s, κ r s = κ s r) :
    (∑ m, (p m ^ 2 + q m ^ 2)) *
        ((∑ r, ∑ s, (κ r s * (β₁ r ^ 2 + β₂ r ^ 2 + (β₁ s ^ 2 + β₂ s ^ 2)) -
            2 * (β₁ r * (K₁ r s * β₁ s - K₂ r s * β₂ s) + β₂ r * (K₁ r s * β₂ s + K₂ r s * β₁ s)))) +
          2 * ∑ r, (β₁ r ^ 2 + β₂ r ^ 2) * (Lg - ∑ s, κ r s)) +
      2 * ((∑ m, (p m ^ 2 + q m ^ 2)) * (∑ m, (c₁ m ^ 2 + c₂ m ^ 2)) -
          ((∑ m, (p m * c₁ m + q m * c₂ m)) ^ 2 + (∑ m, (p m * c₂ m - q m * c₁ m)) ^ 2)) =
      2 * (∑ r, (β₁ r ^ 2 + β₂ r ^ 2)) * (Lg * (∑ m, (p m ^ 2 + q m ^ 2)) - ∑ r, (β₁ r ^ 2 + β₂ r ^ 2)) := by
  have hn : ∑ m, (c₁ m ^ 2 + c₂ m ^ 2) =
      ∑ r, ∑ s, (β₁ r * (K₁ r s * β₁ s - K₂ r s * β₂ s) + β₂ r * (K₁ r s * β₂ s + K₂ r s * β₁ s)) := by
    simp only [hK₁, hK₂, hc₁, hc₂]
    exact adj_norm x y β₁ β₂
  have hr : ∑ m, (p m * c₁ m + q m * c₂ m) = ∑ r, (β₁ r ^ 2 + β₂ r ^ 2) := by
    simp only [hc₁, hc₂]
    rw [adj_real x y p q β₁ β₂]
    exact Finset.sum_congr rfl fun r _ => by rw [← hb₁ r, ← hb₂ r]; ring
  have hi : ∑ m, (p m * c₂ m - q m * c₁ m) = 0 := by
    simp only [hc₁, hc₂]
    rw [adj_imag x y p q β₁ β₂]
    exact Finset.sum_eq_zero fun r _ => by rw [← hb₁ r, ← hb₂ r]; ring
  have hsy := sym_sum κ (fun r => β₁ r ^ 2 + β₂ r ^ 2)
    (fun r s => β₁ r * (K₁ r s * β₁ s - K₂ r s * β₂ s) + β₂ r * (K₁ r s * β₂ s + K₂ r s * β₁ s)) Lg hs
  exact master_alg _ _ _ _ _ _ _ _ hsy hn hr hi

end Ring

/-! ## The Gram bound -/

section Gram

variable {ρ ν : ℕ} (X Y : Fin ρ → Fin ν → ZT n) (p q : Fin ν → ZT n)

/-- `Re K_rs`, `K = A A*`. -/
def gK1 (r s : Fin ρ) : ZT n := ZT.sumFin fun m => X r m * X s m + Y r m * Y s m
/-- `Im K_rs`. -/
def gK2 (r s : Fin ρ) : ZT n := ZT.sumFin fun m => Y r m * X s m - X r m * Y s m
/-- `Re (A a)_r`. -/
def gb1 (r : Fin ρ) : ZT n := ZT.sumFin fun m => X r m * p m - Y r m * q m
/-- `Im (A a)_r`. -/
def gb2 (r : Fin ρ) : ZT n := ZT.sumFin fun m => X r m * q m + Y r m * p m
/-- `Re (A* A a)_m`. -/
def gc1 (m : Fin ν) : ZT n := ZT.sumFin fun r => X r m * gb1 X Y p q r + Y r m * gb2 X Y p q r
/-- `Im (A* A a)_m`. -/
def gc2 (m : Fin ν) : ZT n := ZT.sumFin fun r => X r m * gb2 X Y p q r - Y r m * gb1 X Y p q r

/-- The rational Gram certificate: `|K_rs|² ≤ k_rs²`, `k` symmetric and `Σ_s k_rs ≤ L` give
`Σ_r |(A a)_r|² ≤ L Σ_m |a_m|²`. -/
theorem gram_bound (k : Fin ρ → Fin ρ → PTm n) (L : PTm n)
    (hK : ∀ r s, Γ ⊢[PRAAx] zle (ZT.sq (gK1 X Y r s) + ZT.sq (gK2 X Y r s)) (ZT.ofNat (k r s * k r s)))
    (hsym : ∀ r s, Γ ⊢[PRAAx] k r s ≐ k s r)
    (hL : ∀ r, Γ ⊢[PRAAx] le (nsum fun s => k r s) L) :
    Γ ⊢[PRAAx] zle (ZT.sumFin fun r => ZT.sq (gb1 X Y p q r) + ZT.sq (gb2 X Y p q r))
      (ZT.ofNat L * ZT.sumFin fun m => ZT.sq (p m) + ZT.sq (q m)) := by
  -- the pair inequalities and the Cauchy–Schwarz inequality
  have hp : ∀ r s, Γ ⊢[PRAAx] zle
      (ZT.natLit 2 * (gb1 X Y p q r * (gK1 X Y r s * gb1 X Y p q s - gK2 X Y r s * gb2 X Y p q s) +
        gb2 X Y p q r * (gK1 X Y r s * gb2 X Y p q s + gK2 X Y r s * gb1 X Y p q s)))
      (ZT.ofNat (k r s) * (ZT.sq (gb1 X Y p q r) + ZT.sq (gb2 X Y p q r) +
        (ZT.sq (gb1 X Y p q s) + ZT.sq (gb2 X Y p q s)))) := fun r s => pair_free _ _ _ _ (hK r s)
  have cs := gauss_cs (Γ := Γ) p q (gc1 X Y p q) (gc2 X Y p q)
  -- nonnegativity of the certificate
  have nnPa : Nonneg Γ (∑ m, (ZT.toZ Γ (p m) ^ 2 + ZT.toZ Γ (q m) ^ 2)) :=
    nn_sum _ _ fun m _ => nn_add (nn_zsq _) (nn_zsq _)
  have nnBt : Nonneg Γ (∑ r, (ZT.toZ Γ (gb1 X Y p q r) ^ 2 + ZT.toZ Γ (gb2 X Y p q r) ^ 2)) :=
    nn_sum _ _ fun r _ => nn_add (nn_zsq _) (nn_zsq _)
  have nn1 : Nonneg Γ ((∑ r, ∑ s, zsl (hp r s)) +
      2 * ∑ r, (ZT.toZ Γ (gb1 X Y p q r) ^ 2 + ZT.toZ Γ (gb2 X Y p q r) ^ 2) * sl (hL r)) :=
    nn_add (nn_sum _ _ fun r _ => nn_sum _ _ fun s _ => nn_zsl _)
      (nn_mul (nn_ofNat 2) (nn_sum _ _ fun r _ => nn_mul (nn_add (nn_zsq _) (nn_zsq _)) (nn_sl _)))
  have nnAll := nn_add (nn_mul nnPa nn1) (nn_mul (nn_ofNat 2) (nn_zsl cs))
  -- the certificate identity
  have key := gram_ring (fun r m => ZT.toZ Γ (X r m)) (fun r m => ZT.toZ Γ (Y r m)) (fun m => ZT.toZ Γ (p m))
    (fun m => ZT.toZ Γ (q m)) (fun r => ZT.toZ Γ (gb1 X Y p q r)) (fun r => ZT.toZ Γ (gb2 X Y p q r))
    (fun r s => ZT.toZ Γ (gK1 X Y r s)) (fun r s => ZT.toZ Γ (gK2 X Y r s))
    (fun m => ZT.toZ Γ (gc1 X Y p q m)) (fun m => ZT.toZ Γ (gc2 X Y p q m))
    (fun r s => Groth.ι (Q.mk Γ (k r s))) (Groth.ι (Q.mk Γ L))
    (fun r => by simp only [gb1, ZT.toZ_sumFin, ZT.toZ_sub, ZT.toZ_mul])
    (fun r => by simp only [gb2, ZT.toZ_sumFin, ZT.toZ_add, ZT.toZ_mul])
    (fun r s => by simp only [gK1, ZT.toZ_sumFin, ZT.toZ_add, ZT.toZ_mul])
    (fun r s => by simp only [gK2, ZT.toZ_sumFin, ZT.toZ_sub, ZT.toZ_mul])
    (fun m => by simp only [gc1, ZT.toZ_sumFin, ZT.toZ_add, ZT.toZ_mul])
    (fun m => by simp only [gc2, ZT.toZ_sumFin, ZT.toZ_sub, ZT.toZ_mul])
    (fun r s => natEq (hsym r s))
  have eqAll : (∑ m, (ZT.toZ Γ (p m) ^ 2 + ZT.toZ Γ (q m) ^ 2)) *
        ((∑ r, ∑ s, zsl (hp r s)) +
          2 * ∑ r, (ZT.toZ Γ (gb1 X Y p q r) ^ 2 + ZT.toZ Γ (gb2 X Y p q r) ^ 2) * sl (hL r)) +
      2 * zsl cs =
      2 * (∑ r, (ZT.toZ Γ (gb1 X Y p q r) ^ 2 + ZT.toZ Γ (gb2 X Y p q r) ^ 2)) *
        (Groth.ι (Q.mk Γ L) * (∑ m, (ZT.toZ Γ (p m) ^ 2 + ZT.toZ Γ (q m) ^ 2)) -
          ∑ r, (ZT.toZ Γ (gb1 X Y p q r) ^ 2 + ZT.toZ Γ (gb2 X Y p q r) ^ 2)) := by
    simp only [zsl_def, sl_def, ZT.toZ_mul, ZT.toZ_add, ZT.toZ_sub, ZT.toZ_sq, ZT.toZ_natLit, ZT.toZ_ofNat,
      ZT.toZ_sumFin, Nat.cast_ofNat, toG_nsum]
    exact key
  -- natural witnesses and the cancellation of `2 ‖b‖²`
  obtain ⟨w, hw⟩ := nnAll
  obtain ⟨t, ht⟩ := nnBt
  obtain ⟨s, hs⟩ := nn_mul (nn_term (Γ := Γ) L) nnPa
  rw [eqAll, ht, hs] at hw
  have hnat : Γ ⊢[PRAAx] num 2 * (t * s) ≐ num 2 * (t * t) + w := by
    apply deriveNat
    simp only [Q.mk_add, Q.mk_mul, Q.mk_num, map_add, map_mul, map_natCast, Nat.cast_ofNat, map_ofNat]
    linear_combination hw
  have h3 : Γ ⊢[PRAAx] le (t * t) (t * s) := le_of_two_mul (le_of_eq_add (d := w) hnat)
  have hts : Γ ⊢[PRAAx] le t s := by
    refine .orE (zero_or_succ t) ?_ ?_
    · exact le_congr (Prf.hyp0 : ((t ≐ zero) :: Γ) ⊢[PRAAx] t ≐ zero).eqSymm (.eqRefl s) (zero_le s)
    · have ht' : ((t ≐ succ (pred t)) :: Γ) ⊢[PRAAx] t ≐ succ (pred t) := Prf.hyp0
      exact mul_le_cancel (le_congr (congrMul ht' (.eqRefl _)) (congrMul ht' (.eqRefl _)) h3.wk)
  refine zle_of_comb (sl hts) ?_ (nn_sl hts)
  simp only [sl_def, ZT.toZ_mul, ZT.toZ_ofNat, ZT.toZ_sumFin, ZT.toZ_add, ZT.toZ_sq]
  rw [ht, hs]

end Gram

end LeanProofs.IPRA.AnalyticNumberTheory.GramBound
