import Mathlib.LinearAlgebra.Vandermonde
import IPRADerivations.Core.IntCancel
import IPRADerivations.Foundations.EliminationRoot
import IPRADerivations.Geometry.TetrahedralGram

/-!
# The Vandermonde determinant and the finite root bound (`ipra_resources_and_elimination_2026-11-15`, `lem:elim-shear`, `lem:elim-fibre`)

Packet: `foundations/ipra_resources_and_elimination_2026-11-15`, Section 5. In the proof of
`lem:elim-shear`: "We recall the finite root bound in the form needed here. If a nonzero
degree-`r` rational polynomial vanishes at distinct supplied numbers `t_1, …, t_s`, ... `s ≤ r`."
In the proof of `lem:elim-fibre`: "`det W = ∏_{i<j} (v_j − v_i) ≠ 0`. The Vandermonde formula is
itself a finite polynomial identity".

Derived for integer terms and every size `k` (a parameter of the Lean statements):

* `vand v`, `pairProd v`: the Vandermonde matrix `(v_i^j)` and the product
  `∏_i ∏_j [i < j] (v_j − v_i)` as integer terms;
* `vandermonde_det`: `det (vand v) = pairProd v`;
* `one_ne`, `mul_ne`, `prodFin_ne`: a product of nonzero integer terms is nonzero (the ring of
  differences is not a domain, so this is derived in the object theory by `Core/IntCancel`);
* `vandermonde_ne`: if `v_j − v_i ≠ 0` whenever `i < j`, then `det (vand v) ≠ 0`;
* `right_null_ring`, `root_bound`: the finite root bound. If the polynomial with coefficients
  `c_0, …, c_{k−1}` vanishes at `k` pairwise distinct points `v_0, …, v_{k−1}`, then every
  coefficient is zero. Equivalently, a polynomial of degree at most `r` with a nonzero
  coefficient has at most `r` distinct roots among any supplied list.

Not derived: the synthetic-division form of the argument, the block matrix `W` of
`lem:elim-fibre` and the divisibility `(U − u)^r ∣ R(U)`.
-/

namespace LeanProofs.IPRA.Foundations.VandermondeDeterminant

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.NullVectorDeterminant
open LeanProofs.IPRA.Foundations.EliminationRoot (vpow toZ_vpow)
open LeanProofs.IPRA.Geometry.TetrahedralGram (prodFin toZ_prodFin)
open Syn Matrix
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

section Ring

variable {R : Type*} [CommRing R] {k : ℕ}

/-- The Vandermonde determinant with the product over pairs written with a test. -/
theorem vandermonde_ring (v : Fin k → R) :
    (Matrix.vandermonde v).det = ∏ i : Fin k, ∏ j : Fin k, if i < j then v j - v i else 1 := by
  rw [Matrix.det_vandermonde]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]

/-- A right null vector annihilates the determinant. -/
theorem right_null_ring (M : Matrix (Fin k) (Fin k) R) (c : Fin k → R) (h : M *ᵥ c = 0)
    (i : Fin k) : M.det * c i = 0 := by
  have h1 : (M.det • (1 : Matrix (Fin k) (Fin k) R)) *ᵥ c = 0 := by
    rw [← Matrix.adjugate_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  have h2 := congrFun h1 i
  rw [Matrix.smul_mulVec, Matrix.one_mulVec] at h2
  simpa using h2

end Ring

variable {n : ℕ} {Γ : List (Fm PTm n)} {k : ℕ}

/-- The Vandermonde matrix `(v_i^j)`. -/
def vand (v : Vec k n) : Mat k n := fun i j => vpow (v i) j

/-- `∏_{i<j} (v_j − v_i)`, as a product over all pairs with a test. -/
def pairProd (v : Vec k n) : ZT n :=
  prodFin fun i => prodFin fun j => if i < j then v j - v i else ZT.natLit 1

theorem toZ_vand (v : Vec k n) : Mat.toZ Γ (vand v) = Matrix.vandermonde (Vec.toZ Γ v) := by
  ext i j
  simp [vand, Mat.toZ, Vec.toZ, toZ_vpow, Matrix.vandermonde_apply]

theorem toZ_pairProd (v : Vec k n) :
    ZT.toZ Γ (pairProd v) =
      ∏ i : Fin k, ∏ j : Fin k, if i < j then Vec.toZ Γ v j - Vec.toZ Γ v i else 1 := by
  unfold pairProd
  rw [toZ_prodFin]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [toZ_prodFin]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> simp [Vec.toZ]

/-- The Vandermonde formula: `det (v_i^j) = ∏_{i<j} (v_j − v_i)`. -/
theorem vandermonde_det (v : Vec k n) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det (vand v)) (pairProd v) :=
  ZT.derive (by
    rw [Mat.toZ_det, toZ_vand, toZ_pairProd]
    exact vandermonde_ring _)

/-! ## Nonvanishing -/

/-- The numeral `1` is not zero. -/
theorem one_ne : Γ ⊢[PRAAx] neg (ZT.eq (ZT.natLit 1 : ZT n) (ZT.natLit 0)) := by
  refine .impI (succ_ne_zero' _ (a := num 0) ?_)
  have h : (ZT.eq (ZT.natLit 1 : ZT n) (ZT.natLit 0) :: Γ) ⊢[PRAAx]
      succ (num 0) + zero ≐ zero + zero := Prf.hyp0
  exact (add_zero _).eqSymm.eqTrans (h.eqTrans (zero_add _))

/-- A product of two nonzero integer terms is nonzero. -/
theorem mul_ne {X K : ZT n} (hX : Γ ⊢[PRAAx] neg (ZT.eq X (ZT.natLit 0)))
    (hK : Γ ⊢[PRAAx] neg (ZT.eq K (ZT.natLit 0))) :
    Γ ⊢[PRAAx] neg (ZT.eq (X * K) (ZT.natLit 0)) :=
  .impI (.impE hK.wk (zt_mul_cancel_left hX.wk Prf.hyp0))

/-- A finite product of nonzero integer terms is nonzero. -/
theorem prodFin_ne : {k : ℕ} → {f : Fin k → ZT n} →
    (∀ i, Γ ⊢[PRAAx] neg (ZT.eq (f i) (ZT.natLit 0))) →
    (Γ ⊢[PRAAx] neg (ZT.eq (prodFin f) (ZT.natLit 0)))
  | 0, _, _ => one_ne
  | _ + 1, _, h => mul_ne (h 0) (prodFin_ne fun i => h i.succ)

/-- A nonvanishing statement transported along an equation of integer terms. -/
theorem ne_congr {X Y : ZT n} (e : Γ ⊢[PRAAx] ZT.eq X Y)
    (h : Γ ⊢[PRAAx] neg (ZT.eq Y (ZT.natLit 0))) : Γ ⊢[PRAAx] neg (ZT.eq X (ZT.natLit 0)) := by
  refine .impI (.impE h.wk (ZT.derive ?_))
  have e₁ := ZT.toZ_eq (e.wk (ψ := ZT.eq X (ZT.natLit 0)))
  have e₂ := ZT.toZ_eq (Prf.hyp0 (Γ := Γ) (φ := ZT.eq X (ZT.natLit 0)))
  rw [← e₁, e₂]

/-- `det W ≠ 0` for pairwise distinct points. -/
theorem vandermonde_ne {v : Vec k n}
    (hv : ∀ i j, i < j → (Γ ⊢[PRAAx] neg (ZT.eq (v j - v i) (ZT.natLit 0)))) :
    Γ ⊢[PRAAx] neg (ZT.eq (Mat.det (vand v)) (ZT.natLit 0)) := by
  refine ne_congr (vandermonde_det v) (prodFin_ne fun i => prodFin_ne fun j => ?_)
  by_cases h : i < j
  · rw [if_pos h]
    exact hv i j h
  · rw [if_neg h]
    exact one_ne

/-- The finite root bound: a polynomial with `k` coefficients that vanishes at `k` pairwise
distinct points has all coefficients zero. -/
theorem root_bound {v c : Vec k n}
    (hv : ∀ i j, i < j → (Γ ⊢[PRAAx] neg (ZT.eq (v j - v i) (ZT.natLit 0))))
    (hz : ∀ i, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => vpow (v i) j * c j) (ZT.natLit 0))
    (j : Fin k) : Γ ⊢[PRAAx] ZT.eq (c j) (ZT.natLit 0) := by
  have hnull : Matrix.vandermonde (Vec.toZ Γ v) *ᵥ Vec.toZ Γ c = 0 := by
    funext i
    have e := ZT.toZ_eq (hz i)
    simp only [ZT.toZ_sumFin, ZT.toZ_mul, toZ_vpow, ZT.toZ_natLit, Nat.cast_zero] at e
    simpa [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, Vec.toZ] using e
  have h0 : Γ ⊢[PRAAx] ZT.eq (Mat.det (vand v) * c j) (ZT.natLit 0) :=
    ZT.derive (by
      rw [ZT.toZ_mul, Mat.toZ_det, toZ_vand, ZT.toZ_natLit, Nat.cast_zero]
      exact right_null_ring _ _ hnull j)
  exact zt_mul_cancel_left (vandermonde_ne hv) h0

end LeanProofs.IPRA.Foundations.VandermondeDeterminant
