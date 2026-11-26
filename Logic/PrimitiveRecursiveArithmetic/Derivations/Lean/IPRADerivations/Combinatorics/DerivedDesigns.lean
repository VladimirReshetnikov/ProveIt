import IPRADerivations.Core.CertificateTactics

/-!
# Derived and residual designs: replication and incidence counts

Packet: `combinatorics/Combinatorics-iPRA`, `structure.tex`, result 42 ("Descent, incidence counts, and derived
designs"), for `t = 2`: "the blocks through a specified point, with that point deleted, form a
`(t − 1)`-`(v − 1, k − 1, λ)` design. The blocks missing the point form a `(t − 1)`-design with block size `k`
and parameter `λ_{t−1} − λ`". A design on `v + 1` points is an incidence matrix `M` of integer terms, with
replication `r`, block size `k` and pair count `λ`; `p` is the specified point. As iPRA derivations:

* `residual_replication`: a point `i` lies in `∑_B M_{iB} (1 − M_{pB}) = r − λ` blocks missing `p`;
* `derived_count`: `v λ = r (k − 1)`, the incident pairs of the derived design (`v` points of replication `λ`,
  `r` blocks of size `k − 1`), from `r k = r + v λ` (`Combinatorics/DesignCounts.replication_count`);
* `residual_count`: `v (r − λ) = (b − r) k`, the incident pairs of the residual design (`v` points of
  replication `r − λ`, `b − r` blocks of size `k`), from `(v + 1) r = b k` and `r k = r + v λ`;
* `symmetric_lambda`: in a symmetric design (`r = k`), `λ v = k (k − 1)`.

Not derived: the descent for `t > 2` with its binomial factors, and the cancellation giving `r = k` from
`b = v + 1`.
-/

namespace LeanProofs.IPRA.Combinatorics.DerivedDesigns

open_ipra

variable {n v b : ℕ} {Γ : List (Fm PTm n)}

/-- A point `i` lies in `r − λ` blocks that miss `p`. -/
theorem residual_replication (M : Fin (v + 1) → Fin b → ZT n) (r lam : ZT n) (i p : Fin (v + 1))
    (hr : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => M i B) r)
    (hpair : Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => M i B * M p B) lam) :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun B => M i B * (ZT.natLit 1 - M p B)) (r - lam) := by
  have e1 := ZT.toZ_eq hr
  have e2 := ZT.toZ_eq hpair
  simp only [ZT.toZ_sumFin, ZT.toZ_mul] at e1 e2
  have h : ∀ B, ZT.toZ Γ (M i B) * (1 - ZT.toZ Γ (M p B)) =
      ZT.toZ Γ (M i B) - ZT.toZ Γ (M i B) * ZT.toZ Γ (M p B) := fun B => by ring
  apply ZT.derive
  simp only [ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_natLit, Nat.cast_one]
  rw [Finset.sum_congr rfl fun B _ => h B, Finset.sum_sub_distrib, e1, e2]

/-- The derived design: `v λ = r (k − 1)`. -/
theorem derived_count {r k lam : ZT n}
    (h2 : Γ ⊢[PRAAx] ZT.eq (r * k) (r + ZT.natLit v * lam)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit v * lam) (r * (k - ZT.natLit 1)) := by
  ipra_lc -ZT.toZ_eq h2

/-- The residual design: `v (r − λ) = (b − r) k`. -/
theorem residual_count {r k lam : ZT n}
    (h1 : Γ ⊢[PRAAx] ZT.eq (ZT.natLit (v + 1) * r) (ZT.natLit b * k))
    (h2 : Γ ⊢[PRAAx] ZT.eq (r * k) (r + ZT.natLit v * lam)) :
    Γ ⊢[PRAAx] ZT.eq (ZT.natLit v * (r - lam)) ((ZT.natLit b - r) * k) := by
  ipra_lc [Nat.cast_add] ZT.toZ_eq h1 + ZT.toZ_eq h2

/-- A symmetric design: `λ v = k (k − 1)`. -/
theorem symmetric_lambda {r k lam : ZT n} (hrk : Γ ⊢[PRAAx] ZT.eq r k)
    (h2 : Γ ⊢[PRAAx] ZT.eq (r * k) (r + ZT.natLit v * lam)) :
    Γ ⊢[PRAAx] ZT.eq (lam * ZT.natLit v) (k * (k - ZT.natLit 1)) := by
  ipra_lc (ZT.toZ Γ k - 1) * ZT.toZ_eq hrk - ZT.toZ_eq h2

end LeanProofs.IPRA.Combinatorics.DerivedDesigns
