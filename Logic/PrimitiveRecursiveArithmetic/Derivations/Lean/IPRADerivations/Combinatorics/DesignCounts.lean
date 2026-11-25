import IPRADerivations.AnalyticNumberTheory.GramBound
import IPRADerivations.Core.CertificateTactics

/-!
# Incidence counts of a block design and Fisher's quadratic form

Packet: `combinatorics/Combinatorics-iPRA`, `structure.tex`, results 42 ("Descent, incidence counts, and derived
designs"), 43 ("Fisher's inequality") and 44 ("Necessary Steiner triple parameters"). A design is given by its
incidence matrix `M i B` of integer terms (`0/1` in a design), with points `i` and blocks `B` indexed by finite
types of the metatheory; the pair condition is stated through the Gram sums `∑_B M_{iB} M_{jB}`, which are `r` on
the diagonal and `λ` off it. As iPRA derivations:

* `flag_count` (result 42): "Count pairs (point, block through it) to get `bk = vr`";
* `replication_count` (result 42): `r k = r + (v − 1) λ`, that is `r(k − 1) = λ(v − 1)`, on `v + 1` points
  (written `r k = r + v λ`);
* `steiner_replication`, `steiner_blocks` (result 44): for `k = 3`, `λ = 1` on `v + 1` points, `2r = v` and
  `6b = (v + 1) v`: "each point is in `(v − 1)/2` triples, and there are `v(v − 1)/6` triples";
* `fisher_form` (result 43): `∑_B (∑_{i ∈ B} z_i)² = (r − λ) ∑_i z_i² + λ (∑_i z_i)²`;
* `fisher_kernel` (result 43): "If all block sums vanish, scanning the squares on the right shows that all
  coordinates vanish", for `r > λ ≥ 0`.

Not derived: the pigeonhole step from the trivial kernel to `b ≥ v`, the descent for general `t`, the derived and
residual designs, and the residues of `v` modulo `6`.
-/

namespace LeanProofs.IPRA.Combinatorics.DesignCounts

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.GramBound (sq_sum_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n v b : ℕ} {Γ : List (Fm PTm n)}

/-! ## Identities in a commutative ring -/

section Ring

variable {R : Type*} [CommRing R]

/-- Double counting of the incident pairs: `v r = b k`. -/
theorem flags (M : Fin v → Fin b → R) (r k : R) (hr : ∀ i, ∑ B, M i B = r) (hk : ∀ B, ∑ i, M i B = k) :
    (v : R) * r = (b : R) * k := by
  have h1 : ∑ i, ∑ B, M i B = (v : R) * r := by
    rw [Finset.sum_congr rfl fun i _ => hr i, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have h2 : ∑ i, ∑ B, M i B = (b : R) * k := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun B _ => hk B, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [← h1, h2]

/-- A row of the Gram matrix `(r − λ) I + λ J` against a vector. -/
theorem gram_row (r lam : R) (i : Fin v) (f : Fin v → R) :
    ∑ j, (if i = j then r else lam) * f j = (r - lam) * f i + lam * ∑ j, f j := by
  have e : ∀ j, (if i = j then r else lam) * f j = (if i = j then (r - lam) * f j else 0) + lam * f j := by
    intro j
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Splitting off one summand. -/
theorem sum_split (x : Fin v → R) (i : Fin v) : ∑ j, x j = x i + ∑ j, (if i = j then 0 else x j) := by
  have e : ∀ j, x j = (if i = j then x j else 0) + (if i = j then 0 else x j) := by
    intro j
    split_ifs <;> ring
  have h : ∑ j, x j = ∑ j, ((if i = j then x j else 0) + (if i = j then 0 else x j)) :=
    Finset.sum_congr rfl fun j _ => e j
  rw [h, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- `r k = r + v λ` on `v + 1` points: the blocks through `i` contain `r k` incidences, `r` of them at `i`. -/
theorem replication (M : Fin (v + 1) → Fin b → R) (r k lam : R) (i : Fin (v + 1))
    (hk : ∀ B, ∑ j, M j B = k) (hr : ∑ B, M i B = r)
    (hG : ∀ j, ∑ B, M i B * M j B = if i = j then r else lam) : r * k = r + (v : R) * lam := by
  have h1 : ∑ j, ∑ B, M i B * M j B = r * k := by
    have e : ∀ B, ∑ j, M i B * M j B = M i B * k := fun B => by rw [← Finset.mul_sum, hk B]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun B _ => e B, ← Finset.sum_mul, hr]
  have h2 : ∑ j, ∑ B, M i B * M j B = r + (v : R) * lam := by
    have e := gram_row r lam i (fun _ : Fin (v + 1) => (1 : R))
    simp only [_root_.mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e
    rw [Finset.sum_congr rfl fun j _ => hG j, e]
    push_cast
    ring
  rw [← h1, h2]

/-- Fisher's quadratic form. -/
theorem fisher_identity (M : Fin v → Fin b → R) (z : Fin v → R) (r lam : R)
    (hG : ∀ i j, ∑ B, M i B * M j B = if i = j then r else lam) :
    ∑ B, (∑ i, M i B * z i) ^ 2 = (r - lam) * ∑ i, z i ^ 2 + lam * (∑ i, z i) ^ 2 := by
  have h1 : ∀ B, (∑ i, M i B * z i) ^ 2 = ∑ i, ∑ j, M i B * M j B * (z i * z j) := by
    intro B
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ B, ∑ i, ∑ j, M i B * M j B * (z i * z j) =
      ∑ i, ∑ j, (∑ B, M i B * M j B) * (z i * z j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (Finset.sum_mul _ _ _).symm
  have h3 : ∀ i, ∑ j, (∑ B, M i B * M j B) * (z i * z j) =
      (r - lam) * z i ^ 2 + lam * (z i * ∑ j, z j) := by
    intro i
    have e2 : ∀ j, (∑ B, M i B * M j B) * (z i * z j) = (if i = j then r else lam) * (z i * z j) :=
      fun j => by rw [hG i j]
    have e := gram_row r lam i (fun j => z i * z j)
    rw [Finset.sum_congr rfl fun j _ => e2 j, e, ← Finset.mul_sum]
    ring
  have h4 : ∑ i, ((r - lam) * z i ^ 2 + lam * (z i * ∑ j, z j)) =
      (r - lam) * ∑ i, z i ^ 2 + lam * (∑ i, z i) ^ 2 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [Finset.sum_congr rfl fun B _ => h1 B, h2, Finset.sum_congr rfl fun i _ => h3 i, h4]

end Ring

/-! ## The derivations -/

/-- The Gram sums of the incidence matrix, read in the Grothendieck ring. -/
theorem gram_toZ (M : Fin v → Fin b → ZT n) (r lam : ZT n) (i : Fin v)
    (hdiag : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => M i B * M i B) r)
    (hoff : ∀ j, i ≠ j → (Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => M i B * M j B) lam)) (j : Fin v) :
    ∑ B, ZT.toZ Γ (M i B) * ZT.toZ Γ (M j B) = if i = j then ZT.toZ Γ r else ZT.toZ Γ lam := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    have e := ZT.toZ_eq hdiag
    simpa only [ZT.toZ_sumFin, ZT.toZ_mul] using e
  · rw [if_neg h]
    have e := ZT.toZ_eq (hoff j h)
    simpa only [ZT.toZ_sumFin, ZT.toZ_mul] using e

/-- `v r = b k`: the incident pairs counted by points and by blocks. -/
theorem flag_count (M : Fin v → Fin b → ZT n) (r k : ZT n)
    (hr : ∀ i, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => M i B) r)
    (hk : ∀ B, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => M i B) k) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit v * r) (ZT.natLit b * k) := by
  have hr1 : ∀ i, ∑ B, ZT.toZ Γ (M i B) = ZT.toZ Γ r := fun i => by
    have h := ZT.toZ_eq (hr i)
    simpa only [ZT.toZ_sumFin] using h
  have hk1 : ∀ B, ∑ i, ZT.toZ Γ (M i B) = ZT.toZ Γ k := fun B => by
    have h := ZT.toZ_eq (hk B)
    simpa only [ZT.toZ_sumFin] using h
  apply ZT.derive
  zsimp
  exact flags (fun i B => ZT.toZ Γ (M i B)) _ _ hr1 hk1

/-- `r k = r + v λ` for a point `i` of a design on `v + 1` points. -/
theorem replication_count (M : Fin (v + 1) → Fin b → ZT n) (r k lam : ZT n) (i : Fin (v + 1))
    (hk : ∀ B, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => M j B) k)
    (hr : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => M i B) r)
    (hdiag : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => M i B * M i B) r)
    (hoff : ∀ j, i ≠ j → (Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => M i B * M j B) lam)) :
    Γ ⊢[PRAAx] ZT.eq (r * k) (r + ZT.natLit v * lam) := by
  have hk1 : ∀ B, ∑ j, ZT.toZ Γ (M j B) = ZT.toZ Γ k := fun B => by
    have h := ZT.toZ_eq (hk B)
    simpa only [ZT.toZ_sumFin] using h
  have hr1 : ∑ B, ZT.toZ Γ (M i B) = ZT.toZ Γ r := by
    have h := ZT.toZ_eq hr
    simpa only [ZT.toZ_sumFin] using h
  apply ZT.derive
  zsimp
  exact replication (fun j B => ZT.toZ Γ (M j B)) _ _ _ i hk1 hr1 (gram_toZ M r lam i hdiag hoff)

/-- Steiner triples on `v + 1` points: `2r = v`. -/
theorem steiner_replication {r : ZT n}
    (h : Γ ⊢[PRAAx] ZT.eq (r * ZT.natLit 3) (r + ZT.natLit v * ZT.natLit 1)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * r) (ZT.natLit v) := by
  ipra_lc ZT.toZ_eq h

/-- Steiner triples on `v + 1` points: `6b = (v + 1) v`. -/
theorem steiner_blocks {r : ZT n}
    (h1 : Γ ⊢[PRAAx] ZT.eq (ZT.natLit (v + 1) * r) (ZT.natLit b * ZT.natLit 3))
    (h2 : Γ ⊢[PRAAx] ZT.eq (ZT.natLit 2 * r) (ZT.natLit v)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit 6 * ZT.natLit b) (ZT.natLit (v + 1) * ZT.natLit v) := by
  ipra_lc [Nat.cast_add] (-2 : Groth (Q Γ)) * ZT.toZ_eq h1 + ((v : Groth (Q Γ)) + 1) * ZT.toZ_eq h2

/-- Fisher's quadratic form: `∑_B (∑_i M_{iB} z_i)² = (r − λ) ∑ z_i² + λ (∑ z_i)²`. -/
theorem fisher_form (M : Fin v → Fin b → ZT n) (z : Fin v → ZT n) (r lam : ZT n)
    (hdiag : ∀ i, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => M i B * M i B) r)
    (hoff : ∀ i j, i ≠ j → (Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => M i B * M j B) lam)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => ZT.sq (ZT.sumFin fun i => M i B * z i))
      ((r - lam) * (ZT.sumFin fun i => ZT.sq (z i)) + lam * ZT.sq (ZT.sumFin z)) := by
  have e := fisher_identity (fun i B => ZT.toZ Γ (M i B)) (fun i => ZT.toZ Γ (z i)) _ _
    (fun i j => gram_toZ M r lam i (hdiag i) (hoff i) j)
  beta_reduce at e
  apply ZT.derive
  zsimp
  exact e

/-- The block-sum map has trivial kernel: if every block sum of `z` vanishes and `r > λ ≥ 0`, then `z = 0`. -/
theorem fisher_kernel (M : Fin v → Fin b → ZT n) (z : Fin v → ZT n) (r lam : ZT n)
    (hdiag : ∀ i, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => M i B * M i B) r)
    (hoff : ∀ i j, i ≠ j → (Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => M i B * M j B) lam))
    (hrl : Γ ⊢[PRAAx] zle (lam + ZT.natLit 1) r) (hl : Γ ⊢[PRAAx] zle (ZT.natLit 0) lam)
    (hz : ∀ B, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun i => M i B * z i) (ZT.natLit 0)) (i : Fin v) :
    Γ ⊢[PRAAx] ZT.eq (z i) (ZT.natLit 0) := by
  have hz1 : ∀ B, ∑ j, ZT.toZ Γ (M j B) * ZT.toZ Γ (z j) = 0 := fun B => by
    have h := ZT.toZ_eq (hz B)
    simpa only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_zero] using h
  have e := fisher_identity (fun i B => ZT.toZ Γ (M i B)) (fun i => ZT.toZ Γ (z i)) _ _
    (fun i j => gram_toZ M r lam i (hdiag i) (hoff i) j)
  beta_reduce at e
  have e0 : (ZT.toZ Γ r - ZT.toZ Γ lam) * ∑ j, ZT.toZ Γ (z j) ^ 2 +
      ZT.toZ Γ lam * (∑ j, ZT.toZ Γ (z j)) ^ 2 = 0 := by
    rw [← e]
    refine Finset.sum_eq_zero fun B _ => ?_
    rw [hz1 B]
    ring
  have hsp := sum_split (fun j => ZT.toZ Γ (z j) ^ 2) i
  beta_reduce at hsp
  have hsq : Γ ⊢[PRAAx] zle (ZT.sq (z i)) (ZT.natLit 0) := by
    refine zle_of_comb (zsl hrl * ∑ j, ZT.toZ Γ (z j) ^ 2 +
        ∑ j, (if i = j then 0 else ZT.toZ Γ (z j) ^ 2) + zsl hl * ZT.toZ Γ (ZT.sumFin z) ^ 2) ?_
      (nn_add (nn_add (nn_mul (nn_zsl _) (nn_sum _ _ fun j _ => nn_zsq _))
        (nn_sum _ _ fun j _ => ?_)) (nn_mul (nn_zsl _) (nn_zsq _)))
    · zsimp
      linear_combination (-1 : Groth (Q Γ)) * e0 + hsp
    · show Nonneg Γ (if i = j then 0 else ZT.toZ Γ (z j) ^ 2)
      split_ifs
      · exact nn_zero
      · exact nn_zsq _
  have h2 : Γ ⊢[PRAAx] zle (ZT.sq (z i) + ZT.sq (z i)) (ZT.ofNat (zero * zero)) := by
    ipra_zle (2 * zsl hsq)
  have h0 := (sq_sum_zero (.eqRefl zero) h2).1
  apply ZT.derive
  rw [h0, ZT.toZ_natLit, Nat.cast_zero]

end LeanProofs.IPRA.Combinatorics.DesignCounts
