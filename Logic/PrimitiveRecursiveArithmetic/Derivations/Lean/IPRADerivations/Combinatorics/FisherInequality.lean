import IPRADerivations.Combinatorics.DesignCounts
import IPRADerivations.Combinatorics.Turan
import IPRADerivations.Core.CertificateTactics

/-!
# Fisher's inequality

Packet: `combinatorics/Combinatorics-iPRA`, `structure.tex`, result 43 ("Fisher's inequality"): "A
`2`-`(v, k, λ)` design with `2 ≤ k < v` and `λ > 0` has `b ≥ v`."

The design is its incidence matrix `M i B` of integer terms that are bits, with `p + 1` points and `b + 1`
blocks indexed by finite types of the metatheory, row sums `r`, column sums `k`, and `∑_B M_{iB} M_{jB} = λ` for
`i ≠ j`. As an iPRA derivation:

* `fisher`: for `k ≥ 1`, `r ≥ 1` and `k < p + 1`, the number of points is at most the number of blocks,
  `p + 1 ≤ b + 1`.

The argument is not the packet's (injectivity of the block-sum map on a box of integer vectors and a pigeonhole
count; `Combinatorics/DesignCounts.fisher_kernel` has its first half). It is the variance argument: fix the last
block `B₀` and let `x_B = |B ∩ B₀|` for the other `b` blocks. Then

* `inter_sum`: `∑_{B ≠ B₀} x_B = k r − k`;
* `inter_sq_sum`: `∑_{B ≠ B₀} x_B² = (r − λ) k + λ k² − k²` (Fisher's quadratic form
  `DesignCounts.fisher_identity` at the indicator of `B₀`);

and the finite Cauchy inequality `(∑ x_B)² ≤ b ∑ x_B²` has slack `S` with
`k p S = k r (r − k)(p + 1 − k)²` modulo the incidence identities `(p + 1) r = (b + 1) k` and `r k = r + p λ`.
So `k r (p + 1 − k)² · (r − k) ≥ 0`; the positive factor is cancelled (`znn_of_pos_mul`), giving `r ≥ k`, and
`k (b + 1 − (p + 1)) = (p + 1)(r − k) ≥ 0` gives the claim after cancelling `k`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.FisherInequality

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.DesignCounts (flags replication fisher_identity)
open LeanProofs.IPRA.Combinatorics.Turan (zlt_or_zle)
open Syn
open scoped Fm

variable {n p b v : ℕ} {Γ : List (Fm PTm n)}

/-! ## Identities in a commutative ring -/

section Ring

variable {R : Type*} [CommRing R]

/-- A sum over the blocks other than the last one. -/
theorem others_sum (f : Fin (b + 1) → R) :
    ∑ B : Fin b, f (Fin.castSucc B) = ∑ B, f B - f (Fin.last b) := by
  rw [Fin.sum_univ_castSucc]
  ring

variable (a : Fin v → Fin (b + 1) → R) (r k lam : R)

/-- The Gram sums of a bit matrix with row sums `r` and pair sums `λ`. -/
theorem gram_of_bits (hbit : ∀ i B, a i B * a i B = a i B) (hrow : ∀ i, ∑ B, a i B = r)
    (hpair : ∀ i j, i ≠ j → ∑ B, a i B * a j B = lam) (i j : Fin v) :
    ∑ B, a i B * a j B = if i = j then r else lam := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, Finset.sum_congr rfl fun B _ => hbit i B, hrow i]
  · rw [if_neg h]
    exact hpair i j h

theorem last_sq (hbit : ∀ i B, a i B * a i B = a i B) (hcol : ∑ i, a i (Fin.last b) = k) :
    ∑ i, a i (Fin.last b) * a i (Fin.last b) = k := by
  rw [Finset.sum_congr rfl fun i _ => hbit i (Fin.last b), hcol]

/-- `∑_{B ≠ B₀} |B ∩ B₀| = k r − k`. -/
theorem inter_sum (hbit : ∀ i B, a i B * a i B = a i B) (hrow : ∀ i, ∑ B, a i B = r)
    (hcol : ∑ i, a i (Fin.last b) = k) :
    ∑ B : Fin b, ∑ i, a i (Fin.castSucc B) * a i (Fin.last b) = k * r - k := by
  have hall : ∑ B, ∑ i, a i B * a i (Fin.last b) = k * r := by
    have e : ∀ i, ∑ B, a i B * a i (Fin.last b) = a i (Fin.last b) * r := fun i => by
      rw [← Finset.sum_mul, hrow i]
      ring
    rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => e i, ← Finset.sum_mul, hcol]
  have h := others_sum (fun B => ∑ i, a i B * a i (Fin.last b))
  beta_reduce at h
  rw [h, hall, last_sq a k hbit hcol]

/-- `∑_{B ≠ B₀} |B ∩ B₀|² = (r − λ) k + λ k² − k²`. -/
theorem inter_sq_sum (hbit : ∀ i B, a i B * a i B = a i B)
    (hG : ∀ i j, ∑ B, a i B * a j B = if i = j then r else lam) (hcol : ∑ i, a i (Fin.last b) = k) :
    ∑ B : Fin b, (∑ i, a i (Fin.castSucc B) * a i (Fin.last b)) ^ 2 =
      (r - lam) * k + lam * k ^ 2 - k ^ 2 := by
  have hf := fisher_identity a (fun i => a i (Fin.last b)) r lam hG
  beta_reduce at hf
  have hsq : ∑ i, a i (Fin.last b) ^ 2 = k := by
    have e : ∀ i, a i (Fin.last b) ^ 2 = a i (Fin.last b) := fun i => by rw [sq, hbit i (Fin.last b)]
    rw [Finset.sum_congr rfl fun i _ => e i, hcol]
  have h := others_sum (fun B => (∑ i, a i B * a i (Fin.last b)) ^ 2)
  beta_reduce at h
  rw [h, hf, hsq, hcol, last_sq a k hbit hcol]

end Ring

/-! ## Cancelling a positive factor -/

/-- `1 ≤ P` and `0 ≤ P X` give `0 ≤ X`. -/
theorem znn_of_pos_mul {P X : ZT n} (hP : Γ ⊢[PRAAx] zle (ZT.natLit 1) P)
    (h : Γ ⊢[PRAAx] zle (ZT.natLit 0) (P * X)) : Γ ⊢[PRAAx] zle (ZT.natLit 0) X := by
  refine .orE (zlt_or_zle (ZT.natLit 0) X) ?_ Prf.hyp0
  have hlt : (zle (X + ZT.natLit 1) (ZT.natLit 0) :: Γ) ⊢[PRAAx] zle (X + ZT.natLit 1) (ZT.natLit 0) :=
    Prf.hyp0
  have hP1 := hP.wk (ψ := zle (X + ZT.natLit 1) (ZT.natLit 0))
  have h1 := h.wk (ψ := zle (X + ZT.natLit 1) (ZT.natLit 0))
  ipra_absurd (zsl h1 + zsl hP1 * zsl hlt + zsl hlt + zsl hP1)

/-! ## Fisher's inequality -/

/-- Fisher's inequality: a design with `p + 1` points and `b + 1` blocks, `1 ≤ k < p + 1` and `r ≥ 1`, has at
least as many blocks as points. -/
theorem fisher (M : Fin (p + 1) → Fin (b + 1) → ZT n) (r k lam : ZT n)
    (hbit : ∀ i B, Γ ⊢[PRAAx] ZT.eq (M i B * M i B) (M i B))
    (hrow : ∀ i, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => M i B) r)
    (hcol : ∀ B, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => M i B) k)
    (hpair : ∀ i j, i ≠ j → (Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => M i B * M j B) lam))
    (hk1 : Γ ⊢[PRAAx] zle (ZT.natLit 1) k) (hr1 : Γ ⊢[PRAAx] zle (ZT.natLit 1) r)
    (hkv : Γ ⊢[PRAAx] zle (k + ZT.natLit 1) (ZT.natLit (p + 1))) :
    Γ ⊢[PRAAx] zle (ZT.natLit (p + 1)) (ZT.natLit (b + 1)) := by
  have hbit1 : ∀ i B, ZT.toZ Γ (M i B) * ZT.toZ Γ (M i B) = ZT.toZ Γ (M i B) := fun i B => by
    have e := ZT.toZ_eq (hbit i B)
    simpa only [ZT.toZ_mul] using e
  have hrow1 : ∀ i, ∑ B, ZT.toZ Γ (M i B) = ZT.toZ Γ r := fun i => by
    have e := ZT.toZ_eq (hrow i)
    simpa only [ZT.toZ_sumFin] using e
  have hcol1 : ∀ B, ∑ i, ZT.toZ Γ (M i B) = ZT.toZ Γ k := fun B => by
    have e := ZT.toZ_eq (hcol B)
    simpa only [ZT.toZ_sumFin] using e
  have hpair1 : ∀ i j, i ≠ j → ∑ B, ZT.toZ Γ (M i B) * ZT.toZ Γ (M j B) = ZT.toZ Γ lam :=
    fun i j h => by
      have e := ZT.toZ_eq (hpair i j h)
      simpa only [ZT.toZ_sumFin, ZT.toZ_mul] using e
  have hG := gram_of_bits (fun i B => ZT.toZ Γ (M i B)) (ZT.toZ Γ r) (ZT.toZ Γ lam) hbit1 hrow1 hpair1
  have h1 : ((p + 1 : ℕ) : Groth (Q Γ)) * ZT.toZ Γ r = ((b + 1 : ℕ) : Groth (Q Γ)) * ZT.toZ Γ k :=
    flags (fun i B => ZT.toZ Γ (M i B)) _ _ hrow1 hcol1
  have h1p := h1
  push_cast at h1p
  have h2 : ZT.toZ Γ r * ZT.toZ Γ k = ZT.toZ Γ r + (p : Groth (Q Γ)) * ZT.toZ Γ lam :=
    replication (fun i B => ZT.toZ Γ (M i B)) _ _ _ 0 hcol1 (hrow1 0) (hG 0)
  have F1 := inter_sum (fun i B => ZT.toZ Γ (M i B)) (ZT.toZ Γ r) (ZT.toZ Γ k) hbit1 hrow1
    (hcol1 (Fin.last b))
  have F2 := inter_sq_sum (fun i B => ZT.toZ Γ (M i B)) (ZT.toZ Γ r) (ZT.toZ Γ k) (ZT.toZ Γ lam) hbit1 hG
    (hcol1 (Fin.last b))
  beta_reduce at F1 F2
  have hc := cauchy_int (Γ := Γ)
    (fun B : Fin b => ZT.sumFin fun i => M i (Fin.castSucc B) * M i (Fin.last b))
  have hk0 : Γ ⊢[PRAAx] zle (ZT.natLit 0) k := by
    ipra_zle (zsl hk1 + 1)
  have hpos : Γ ⊢[PRAAx] zle (ZT.natLit 0)
      ((k * r * ZT.sq (ZT.natLit (p + 1) - k)) * (r - k)) := by
    refine zle_of_comb (ZT.toZ Γ k * (p : Groth (Q Γ)) * zsl hc) ?_
      (nn_mul (nn_mul (nn_zle0 hk0) (nn_natCast p)) (nn_zsl _))
    simp only [zsl_def, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_sq, ZT.toZ_natLit, ZT.toZ_sumFin, Nat.cast_zero]
    rw [F1, F2]
    push_cast
    linear_combination
      ((p : Groth (Q Γ)) * (ZT.toZ Γ r * ZT.toZ Γ k - ZT.toZ Γ k ^ 2) +
          (p : Groth (Q Γ)) * ZT.toZ Γ lam * ZT.toZ Γ k * (ZT.toZ Γ k - 1)) * h1p +
        ((((p : Groth (Q Γ)) + 1) * ZT.toZ Γ r - ZT.toZ Γ k) * ZT.toZ Γ k * (ZT.toZ Γ k - 1)) * h2
  have hP : Γ ⊢[PRAAx] zle (ZT.natLit 1) (k * r * ZT.sq (ZT.natLit (p + 1) - k)) := by
    ipra_zle (zsl hk1 + zsl hr1 + zsl hk1 * zsl hr1 + (1 + zsl hk1) * (1 + zsl hr1) * (2 * zsl hkv + zsl hkv * zsl hkv))
  have hrk : Γ ⊢[PRAAx] zle (ZT.natLit 0) (r - k) := znn_of_pos_mul hP hpos
  have hkb : Γ ⊢[PRAAx] zle (ZT.natLit 0) (k * (ZT.natLit (b + 1) - ZT.natLit (p + 1))) := by
    ipra_zle (((p + 1 : ℕ) : Groth (Q Γ)) * zsl hrk) with -h1
  have hfin : Γ ⊢[PRAAx] zle (ZT.natLit 0) (ZT.natLit (b + 1) - ZT.natLit (p + 1)) :=
    znn_of_pos_mul hk1 hkb
  ipra_zle (zsl hfin)

end LeanProofs.IPRA.Combinatorics.FisherInequality
