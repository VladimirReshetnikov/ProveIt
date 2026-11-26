import IPRADerivations.Analysis.DifferentialEquations.EulerPolygons.EulerRefinement
import IPRADerivations.Analysis.DifferentialEquations.EulerPolygons.EulerInterpAlgebra
import IPRADerivations.Core.Division

/-!
# The interpolated Euler polygons and the refinement estimate at every rational point

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/07_ode.tex`. The paper defines, "for
rational `t < 1`, put `j = ⌊nt⌋` and `X_n(t) = X_{n,j} + (t − j/n) B(j/n) X_{n,j}`; `X_n(1) = X_{n,n}`. This
definition uses rational arithmetic, division with remainder, and a bounded recurrence", and
Theorem `thm:ode-produced-refinement` states `eq:ode-produced-refine`, `‖X_n(t) − X_{2n}(t)‖ ≤ C / (2n)`, "for
every rational `t ∈ [0,1]`".

* `polyNum … nn q i ρ k` and `polyDen … nn q i`: numerator and denominator of the polygon of mesh `nn` at the
  point `(i + ρ/q)/nn` of the cell `i`: `(nn q b x + ρ M x) / (nn q b Xd)` for the node value `x / Xd` and the
  matrix `M / b = B(i/nn)`.
* `Pn`, `Pd`: the interpolation program at `t = p/q`: the cell is `quo (nn p) q` and `ρ = rem (nn p) q`
  (`Core/Division`). At `t = 1` the cell is `nn` with `ρ = 0`, and the value is the node value `X_{nn,nn}`.
* `local_node`, `local_first`, `local_second`: the estimate in the local coordinates of a coarse cell: at a
  coarse node (`ρ = 0`, from `euler_refinement`); on the first half (`2ρ ≤ q`, from the node estimates at the fine
  nodes `2i`, `2i + 1` by `EulerInterpAlgebra.interp_first`); on the second half (`q ≤ 2ρ`, from the fine nodes
  `2i + 1`, `2i + 2` by `interp_second`). The convex combination of two majorant values is bounded by the later
  one, because the majorant satisfies `κ u_j ≤ u_{j+1}`; `EulerRefinement.finish` then gives the constant `C`.
* `euler_refinement_at`: `eq:ode-produced-refine` for the programs, at every `p ≤ q`, `q = q' + 1`:
  `2n |Pn(n) Pd(2n) − Pn(2n) Pd(n)| ≤ C Pd(n) Pd(2n)`. The fine cell and remainder are identified by the
  uniqueness of division with remainder (`div_mod_unique`), by the cases `ρ = 0`, `0 < 2ρ < q`, `q ≤ 2ρ`.
  `euler_refinement_at_norm` is the same statement for the maximum norm term `nrm` of the numerator vector.
-/

namespace LeanProofs.IPRA.Analysis.EulerInterpolation

open_ipra
open LeanProofs.IPRA.Foundations.TupleRecursion LeanProofs.IPRA.Foundations.SignedNorms
  LeanProofs.IPRA.Foundations.SignedCone LeanProofs.IPRA.Analysis.EulerProgram
  LeanProofs.IPRA.Analysis.EulerNodeBound LeanProofs.IPRA.Analysis.EulerMajorant
  LeanProofs.IPRA.Analysis.EulerRefinement

variable {n d : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The polygon in the local coordinates of a cell -/

/-- The numerator of the polygon of mesh `nn` at the point `(i + ρ/q)/nn` of the cell `i`. -/
def polyNum (B : Kernel d) (v : Fin d → ZT n) (x nn q i ρ : PTm n) (k : Fin d) : ZT n :=
  ZT.ofNat (nn * q * B.denAt i nn x) * Xn B v i nn x k +
    ZT.ofNat ρ * ZT.sumFin fun l => B.numAt k l i nn x * Xn B v i nn x l

/-- The denominator of the polygon of mesh `nn` on the cell `i`, for points with the denominator `q`. -/
def polyDen (B : Kernel d) (dv x nn q i : PTm n) : PTm n := nn * q * B.denAt i nn x * Xd B dv i nn x

theorem toZ_polyNum (B : Kernel d) (v : Fin d → ZT n) (x nn q i ρ : PTm n) (k : Fin d) :
    ZT.toZ Γ (polyNum B v x nn q i ρ k) =
      𝔞 nn * 𝔞 q * 𝔞 (B.denAt i nn x) * ZT.toZ Γ (Xn B v i nn x k) +
        𝔞 ρ * ∑ l, ZT.toZ Γ (B.numAt k l i nn x) * ZT.toZ Γ (Xn B v i nn x l) := by
  simp only [polyNum, ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat, ZT.toZ_sumFin]
  rw [Q.mk_mul, map_mul, Q.mk_mul, map_mul]

theorem mk_polyDen (B : Kernel d) (dv x nn q i : PTm n) :
    (𝔞 (polyDen B dv x nn q i) : Groth (Q Γ)) = 𝔞 nn * 𝔞 q * 𝔞 (B.denAt i nn x) * 𝔞 (Xd B dv i nn x) := by
  rw [polyDen, Q.mk_mul, map_mul, Q.mk_mul, map_mul, Q.mk_mul, map_mul]

/-- The numerator of the difference of the polygons of the meshes `nn` and `nn'` at two local coordinates. -/
def cellCross (B : Kernel d) (v : Fin d → ZT n) (dv x nn q i ρ nn' i' ρ' : PTm n) (k : Fin d) : ZT n :=
  polyNum B v x nn q i ρ k * ZT.ofNat (polyDen B dv x nn' q i') -
    polyNum B v x nn' q i' ρ' k * ZT.ofNat (polyDen B dv x nn q i)

theorem toZ_cellCross (B : Kernel d) (v : Fin d → ZT n) (dv x nn q i ρ nn' i' ρ' : PTm n) (k : Fin d) :
    ZT.toZ Γ (cellCross B v dv x nn q i ρ nn' i' ρ' k) =
      ZT.toZ Γ (polyNum B v x nn q i ρ k) * 𝔞 (polyDen B dv x nn' q i') -
        ZT.toZ Γ (polyNum B v x nn' q i' ρ' k) * 𝔞 (polyDen B dv x nn q i) := by
  simp only [cellCross, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat]

section Congruence

variable (B : Kernel d) (v : Fin d → ZT n) (dv x q : PTm n) {nn nn' i i' ρ ρ' : PTm n}

theorem congr_polyNum (k : Fin d) (hn : Γ ⊢[PRAAx] nn ≐ nn') (hi : Γ ⊢[PRAAx] i ≐ i')
    (hρ : Γ ⊢[PRAAx] ρ ≐ ρ') :
    ZT.toZ Γ (polyNum B v x nn q i ρ k) = ZT.toZ Γ (polyNum B v x nn' q i' ρ' k) := by
  have e5 : ∑ l, ZT.toZ Γ (B.numAt k l i nn x) * ZT.toZ Γ (Xn B v i nn x l) =
      ∑ l, ZT.toZ Γ (B.numAt k l i' nn' x) * ZT.toZ Γ (Xn B v i' nn' x l) :=
    Finset.sum_congr rfl fun l _ => by rw [B.congrNumAt k l x hi hn, congrXn B v x l hi hn]
  rw [toZ_polyNum, toZ_polyNum, e5, congrXn B v x k hi hn]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (natEq hn) rfl) (natEq (B.congrDenAt x hi hn))) rfl)
    (congrArg₂ (· * ·) (natEq hρ) rfl)

theorem congr_polyDen (hn : Γ ⊢[PRAAx] nn ≐ nn') (hi : Γ ⊢[PRAAx] i ≐ i') :
    (𝔞 (polyDen B dv x nn q i) : Groth (Q Γ)) = 𝔞 (polyDen B dv x nn' q i') := by
  rw [mk_polyDen, mk_polyDen]
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (natEq hn) rfl)
    (natEq (B.congrDenAt x hi hn))) (natEq (congrXd B dv x hi hn))

end Congruence

/-- The estimate in local coordinates, moved to provably equal meshes, cells and remainders. -/
theorem transfer {B : Kernel d} {v : Fin d → ZT n} {dv x q C κ κ' nn mm i j ρ σ nn' mm' i' j' ρ' σ' : PTm n}
    {k : Fin d}
    (h : Γ ⊢[PRAAx] le (κ * abs (cellCross B v dv x nn q i ρ nn' i' ρ' k))
      (C * (polyDen B dv x nn q i * polyDen B dv x nn' q i')))
    (hκ : Γ ⊢[PRAAx] κ' ≐ κ) (hn : Γ ⊢[PRAAx] mm ≐ nn) (hi : Γ ⊢[PRAAx] j ≐ i) (hρ : Γ ⊢[PRAAx] σ ≐ ρ)
    (hn' : Γ ⊢[PRAAx] mm' ≐ nn') (hi' : Γ ⊢[PRAAx] j' ≐ i') (hρ' : Γ ⊢[PRAAx] σ' ≐ ρ') :
    Γ ⊢[PRAAx] le (κ' * abs (cellCross B v dv x mm q j σ mm' j' σ' k))
      (C * (polyDen B dv x mm q j * polyDen B dv x mm' q j')) := by
  refine le_abs_of_bd₀ ((bd_of_le h).congr ?_ ?_)
  · rw [toZ_cellCross, toZ_cellCross, congr_polyNum B v x q k hn hi hρ, congr_polyNum B v x q k hn' hi' hρ',
      congr_polyDen B dv x q hn hi, congr_polyDen B dv x q hn' hi', natEq hκ]
  · simp only [Q.mk_mul, map_mul]
    rw [congr_polyDen B dv x q hn hi, congr_polyDen B dv x q hn' hi']

/-! ## The three cases of a coarse cell -/

section Local

variable {B : Kernel d} {v : Fin d → ZT n} {dv U K L x n₀ i ρ q : PTm n}

/-- At a coarse node (`ρ = 0`): the node estimate over the padded denominators. -/
theorem local_node (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L)
    (hdv : Γ ⊢[PRAAx] lt zero dv) (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv))
    (hi : Γ ⊢[PRAAx] le i (succ n₀)) (k : Fin d) :
    Γ ⊢[PRAAx] le (dbl (succ n₀) *
        abs (cellCross B v dv x (succ n₀) q i zero (dbl (succ n₀)) (dbl i) zero k))
      (Cc K L U * (polyDen B dv x (succ n₀) q i * polyDen B dv x (dbl (succ n₀)) q (dbl i))) := by
  have h := bd_of_le (euler_refinement hK hL hdv hv hi k)
  have z0 : (𝔞 (zero : PTm n) : Groth (Q Γ)) = 0 := by simp only [Q.mk_zero, map_zero]
  refine le_abs_of_bd₀ ((h.smul nnCone (nn_term (succ n₀ * q * B.denAt i (succ n₀) x *
    (dbl (succ n₀) * q * B.denAt (dbl i) (dbl (succ n₀)) x)))).congr ?_ ?_)
  · rw [toZ_errNum, toZ_cellCross, toZ_polyNum, toZ_polyNum, mk_polyDen, mk_polyDen, z0]
    simp only [Q.mk_mul, map_mul]
    ring
  · simp only [Q.mk_mul, map_mul]
    rw [mk_polyDen, mk_polyDen]
    ring

/-- The equations of the fine program on the cell, in the form of `EulerInterpAlgebra`. -/
theorem fine_step (j : PTm n) (r : Fin d) :
    ZT.toZ Γ (Xn B v (succ j) (dbl (succ n₀)) x r) =
      2 * 𝔞 (succ n₀) * 𝔞 (B.denAt j (dbl (succ n₀)) x) * ZT.toZ Γ (Xn B v j (dbl (succ n₀)) x r) +
        ∑ l, ZT.toZ Γ (B.numAt r l j (dbl (succ n₀)) x) * ZT.toZ Γ (Xn B v j (dbl (succ n₀)) x l) := by
  rw [Xn_succ (Γ := Γ) B v j (dbl (succ n₀)) x r, mk_dbl]

theorem fine_den (j : PTm n) :
    (𝔞 (Xd B dv (succ j) (dbl (succ n₀)) x) : Groth (Q Γ)) =
      2 * 𝔞 (succ n₀) * 𝔞 (B.denAt j (dbl (succ n₀)) x) * 𝔞 (Xd B dv j (dbl (succ n₀)) x) := by
  rw [Xd_succ (Γ := Γ) B dv j (dbl (succ n₀)) x, mk_dbl]

/-- On the first half of a coarse cell `i < n` (`2ρ ≤ q`). -/
theorem local_first (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L)
    (hdv : Γ ⊢[PRAAx] lt zero dv) (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv))
    (hi : Γ ⊢[PRAAx] le (succ i) (succ n₀)) (hρ : Γ ⊢[PRAAx] le (dbl ρ) q) (k : Fin d) :
    Γ ⊢[PRAAx] le (dbl (succ n₀) *
        abs (cellCross B v dv x (succ n₀) q i ρ (dbl (succ n₀)) (dbl i) (dbl ρ) k))
      (Cc K L U * (polyDen B dv x (succ n₀) q i * polyDen B dv x (dbl (succ n₀)) q (dbl i))) := by
  have hin : Γ ⊢[PRAAx] le i (succ n₀) := le_trans (le_succ_self i) hi
  have hqρ : Nonneg Γ (𝔞 q - 2 * 𝔞 ρ) := Cone.of_eq (nn_sl hρ) (by rw [sl_def, mk_dbl])
  have pk3 := natEq (pw_succ (Γ := Γ) (dbl (succ n₀)) (succ (succ (dbl i))))
  simp only [Q.mk_mul, map_mul] at pk3
  have u1 := natEq (maj_succ₃ (Γ := Γ) (dbl i) (dbl (succ n₀)) K (Hc K L U))
  simp only [Q.mk_mul, Q.mk_add, map_mul, map_add] at u1
  have hq₁ := fine_den (Γ := Γ) (B := B) (dv := dv) (x := x) (n₀ := n₀) (dbl i)
  -- the node estimates at the fine nodes `2i` and `2i + 1`, at the common scale `κ^{2i+3}`
  have h₀ : ∀ r, Bd (Nonneg Γ) (𝔞 (pw (dbl (succ n₀)) (succ (succ (succ (dbl i))))) *
      (ZT.toZ Γ (Xn B v i (succ n₀) x r) * 𝔞 (Xd B dv (dbl i) (dbl (succ n₀)) x) -
        ZT.toZ Γ (Xn B v (dbl i) (dbl (succ n₀)) x r) * 𝔞 (Xd B dv i (succ n₀) x)))
      (𝔞 (dbl (succ n₀)) * 𝔞 (maj (dbl i) ![dbl (succ n₀), K, Hc K L U] *
        (Xd B dv i (succ n₀) x * Xd B dv (dbl i) (dbl (succ n₀)) x))) := fun r =>
    ((bd_of_le (conjFin_elim (Prf.impE (ref_inv n₀ hK hL hdv hv i) hin) r)).smul nnCone
      (nn_term (dbl (succ n₀)))).congr (by rw [toZ_errNum, pk3]; ring) rfl
  have h₁ : ∀ r, Bd (Nonneg Γ) (𝔞 (pw (dbl (succ n₀)) (succ (succ (succ (dbl i))))) *
      ((2 * 𝔞 (succ n₀) * 𝔞 (B.denAt i (succ n₀) x) * ZT.toZ Γ (Xn B v i (succ n₀) x r) +
          ∑ l, ZT.toZ Γ (B.numAt r l i (succ n₀) x) * ZT.toZ Γ (Xn B v i (succ n₀) x l)) *
          𝔞 (Xd B dv (succ (dbl i)) (dbl (succ n₀)) x) -
        ZT.toZ Γ (Xn B v (succ (dbl i)) (dbl (succ n₀)) x r) *
          (2 * 𝔞 (succ n₀) * 𝔞 (B.denAt i (succ n₀) x) * 𝔞 (Xd B dv i (succ n₀) x))))
      (𝔞 (maj (succ (dbl i)) ![dbl (succ n₀), K, Hc K L U] *
        (dbl (succ n₀) * B.denAt i (succ n₀) x * Xd B dv i (succ n₀) x *
          Xd B dv (succ (dbl i)) (dbl (succ n₀)) x))) := fun r =>
    (bd_of_le (ref_odd hK hL hdv hv hi r)).congr (by rw [toZ_oddNum]) rfl
  have R := EulerInterpAlgebra.interp_first (P := Nonneg Γ) nnCone
    (y := fun r => 2 * 𝔞 (succ n₀) * 𝔞 (B.denAt i (succ n₀) x) * ZT.toZ Γ (Xn B v i (succ n₀) x r) +
      ∑ l, ZT.toZ Γ (B.numAt r l i (succ n₀) x) * ZT.toZ Γ (Xn B v i (succ n₀) x l))
    (pc := fun r => ZT.toZ Γ (polyNum B v x (succ n₀) q i ρ r))
    (pf := fun r => ZT.toZ Γ (polyNum B v x (dbl (succ n₀)) q (dbl i) (dbl ρ) r))
    (nn_term (succ n₀)) (nn_term (B.denAt i (succ n₀) x)) (nn_term (B.denAt (dbl i) (dbl (succ n₀)) x))
    (nn_term q) (nn_term ρ) hqρ (fun _ => rfl) (fun r => fine_step (dbl i) r) hq₁
    (fun r => toZ_polyNum B v x (succ n₀) q i ρ r)
    (fun r => by rw [toZ_polyNum, mk_dbl, mk_dbl]) h₀ h₁ k
  -- the convex combination of `u_{2i}` and `u_{2i+1}` is bounded by `u_{2i+1}`
  have hmono : Nonneg Γ (𝔞 (maj (succ (dbl i)) ![dbl (succ n₀), K, Hc K L U] *
      (polyDen B dv x (succ n₀) q i * polyDen B dv x (dbl (succ n₀)) q (dbl i))) -
      𝔞 q * ((𝔞 q - 2 * 𝔞 ρ) * (2 * 𝔞 (succ n₀) * 𝔞 (succ n₀) * 𝔞 (B.denAt i (succ n₀) x) *
          𝔞 (B.denAt (dbl i) (dbl (succ n₀)) x)) *
          (𝔞 (dbl (succ n₀)) * 𝔞 (maj (dbl i) ![dbl (succ n₀), K, Hc K L U] *
            (Xd B dv i (succ n₀) x * Xd B dv (dbl i) (dbl (succ n₀)) x))) +
        𝔞 ρ * 𝔞 (maj (succ (dbl i)) ![dbl (succ n₀), K, Hc K L U] *
          (dbl (succ n₀) * B.denAt i (succ n₀) x * Xd B dv i (succ n₀) x *
            Xd B dv (succ (dbl i)) (dbl (succ n₀)) x)))) := by
    have hz : Nonneg Γ (𝔞 q * (2 * 𝔞 (succ n₀)) * 𝔞 (B.denAt i (succ n₀) x) *
        𝔞 (B.denAt (dbl i) (dbl (succ n₀)) x) * 𝔞 (Xd B dv i (succ n₀) x) *
        𝔞 (Xd B dv (dbl i) (dbl (succ n₀)) x) * 𝔞 (succ n₀) * (𝔞 q - 2 * 𝔞 ρ) *
        (𝔞 K * 𝔞 (maj (dbl i) ![dbl (succ n₀), K, Hc K L U]) +
          𝔞 (pw (dbl (succ n₀)) (succ (dbl i))) * 𝔞 (Hc K L U))) := by
      ipra_nonneg
    refine Cone.of_eq hz ?_
    simp only [Q.mk_mul, map_mul]
    rw [mk_polyDen, mk_polyDen, u1, hq₁, mk_dbl]
    ring
  have hfin : Γ ⊢[PRAAx] le (pw (dbl (succ n₀)) (succ (succ (succ (dbl i)))) *
      abs (cellCross B v dv x (succ n₀) q i ρ (dbl (succ n₀)) (dbl i) (dbl ρ) k))
      (maj (succ (dbl i)) ![dbl (succ n₀), K, Hc K L U] *
        (polyDen B dv x (succ n₀) q i * polyDen B dv x (dbl (succ n₀)) q (dbl i))) := by
    refine le_abs_of_bd₀ ((R.mono nnCone hmono).congr ?_ rfl)
    rw [toZ_cellCross, mk_polyDen, mk_polyDen, mk_dbl]
  have hN : Γ ⊢[PRAAx] succ (dbl i) + succ (dbl (monus (succ n₀) (succ i))) ≐ succ (n₀ + succ n₀) := by
    have w := natEq (eq_add_of_le hi)
    show Γ ⊢[PRAAx] succ (i + i) + succ (monus (succ n₀) (succ i) + monus (succ n₀) (succ i)) ≐
      succ (n₀ + succ n₀)
    apply deriveNat; ipra_simps; linear_combination (-2 : Groth (Q Γ)) * w
  exact finish (dbl_succ_eq n₀) hN hfin

/-- On the second half of a coarse cell `i < n` (`q ≤ 2ρ`, `ρ ≤ q`). -/
theorem local_second (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L)
    (hdv : Γ ⊢[PRAAx] lt zero dv) (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv))
    (hi : Γ ⊢[PRAAx] le (succ i) (succ n₀)) (hρ₁ : Γ ⊢[PRAAx] le q (dbl ρ)) (hρ₂ : Γ ⊢[PRAAx] le ρ q)
    (k : Fin d) :
    Γ ⊢[PRAAx] le (dbl (succ n₀) *
        abs (cellCross B v dv x (succ n₀) q i ρ (dbl (succ n₀)) (succ (dbl i)) (monus (dbl ρ) q) k))
      (Cc K L U * (polyDen B dv x (succ n₀) q i * polyDen B dv x (dbl (succ n₀)) q (succ (dbl i)))) := by
  have hqρ : Nonneg Γ (𝔞 q - 𝔞 ρ) := Cone.of_eq (nn_sl hρ₂) (sl_def hρ₂)
  have hρeq : (𝔞 (monus (dbl ρ) q) : Groth (Q Γ)) = 2 * 𝔞 ρ - 𝔞 q := by
    have w := natEq (eq_add_of_le hρ₁)
    simp only [Q.mk_add, map_add] at w
    rw [mk_dbl] at w
    linear_combination -w
  have ej : Γ ⊢[PRAAx] dbl (succ i) ≐ succ (succ (dbl i)) := by
    show Γ ⊢[PRAAx] succ i + succ i ≐ succ (succ (i + i))
    ipra_ring
  have pk4 := natEq (pw_succ (Γ := Γ) (dbl (succ n₀)) (succ (succ (succ (dbl i)))))
  simp only [Q.mk_mul, map_mul] at pk4
  have pe := natEq (congrAp2 powF (congrSucc (congrSucc ej)) (.eqRefl (dbl (succ n₀))) :
    Γ ⊢[PRAAx] pw (dbl (succ n₀)) (succ (succ (dbl (succ i)))) ≐
      pw (dbl (succ n₀)) (succ (succ (succ (succ (dbl i))))))
  have u2 := natEq (maj_succ₃ (Γ := Γ) (succ (dbl i)) (dbl (succ n₀)) K (Hc K L U))
  simp only [Q.mk_mul, Q.mk_add, map_mul, map_add] at u2
  have cU := natEq (congrMaj (Γ := Γ) (ps := ![dbl (succ n₀), K, Hc K L U]) ej fun _ => .eqRefl _)
  have cD := natEq (congrXd (Γ := Γ) B dv x ej (.eqRefl (dbl (succ n₀))))
  have hq₂ := fine_den (Γ := Γ) (B := B) (dv := dv) (x := x) (n₀ := n₀) (succ (dbl i))
  have hD' := Xd_succ (Γ := Γ) B dv i (succ n₀) x
  -- the node estimates at the fine nodes `2i + 1` and `2i + 2`, at the common scale `κ^{2i+4}`
  have h₁ : ∀ r, Bd (Nonneg Γ) (𝔞 (pw (dbl (succ n₀)) (succ (succ (succ (succ (dbl i)))))) *
      ((2 * 𝔞 (succ n₀) * 𝔞 (B.denAt i (succ n₀) x) * ZT.toZ Γ (Xn B v i (succ n₀) x r) +
          ∑ l, ZT.toZ Γ (B.numAt r l i (succ n₀) x) * ZT.toZ Γ (Xn B v i (succ n₀) x l)) *
          𝔞 (Xd B dv (succ (dbl i)) (dbl (succ n₀)) x) -
        ZT.toZ Γ (Xn B v (succ (dbl i)) (dbl (succ n₀)) x r) *
          (2 * 𝔞 (succ n₀) * 𝔞 (B.denAt i (succ n₀) x) * 𝔞 (Xd B dv i (succ n₀) x))))
      (𝔞 (dbl (succ n₀)) * 𝔞 (maj (succ (dbl i)) ![dbl (succ n₀), K, Hc K L U] *
        (dbl (succ n₀) * B.denAt i (succ n₀) x * Xd B dv i (succ n₀) x *
          Xd B dv (succ (dbl i)) (dbl (succ n₀)) x))) := fun r =>
    ((bd_of_le (ref_odd hK hL hdv hv hi r)).smul nnCone (nn_term (dbl (succ n₀)))).congr
      (by rw [toZ_oddNum, pk4]; ring) rfl
  have h₂ : ∀ r, Bd (Nonneg Γ) (𝔞 (pw (dbl (succ n₀)) (succ (succ (succ (succ (dbl i)))))) *
      (ZT.toZ Γ (Xn B v (succ i) (succ n₀) x r) * 𝔞 (Xd B dv (succ (succ (dbl i))) (dbl (succ n₀)) x) -
        ZT.toZ Γ (Xn B v (succ (succ (dbl i))) (dbl (succ n₀)) x r) * 𝔞 (Xd B dv (succ i) (succ n₀) x)))
      (𝔞 (maj (succ (succ (dbl i))) ![dbl (succ n₀), K, Hc K L U]) *
        (𝔞 (Xd B dv (succ i) (succ n₀) x) * 𝔞 (Xd B dv (succ (succ (dbl i))) (dbl (succ n₀)) x))) := fun r =>
    (bd_of_le (conjFin_elim (Prf.impE (ref_inv n₀ hK hL hdv hv (succ i)) hi) r)).congr
      (by rw [toZ_errNum, congrXn (Γ := Γ) B v x r ej (.eqRefl (dbl (succ n₀))), cD, pe])
      (by simp only [Q.mk_mul, map_mul]; rw [cU, cD])
  have R := EulerInterpAlgebra.interp_second (P := Nonneg Γ) nnCone
    (β := 𝔞 (B.denAt i (succ n₀) x)) (D := 𝔞 (Xd B dv i (succ n₀) x))
    (y := fun r => 2 * 𝔞 (succ n₀) * 𝔞 (B.denAt i (succ n₀) x) * ZT.toZ Γ (Xn B v i (succ n₀) x r) +
      ∑ l, ZT.toZ Γ (B.numAt r l i (succ n₀) x) * ZT.toZ Γ (Xn B v i (succ n₀) x l))
    (pc := fun r => ZT.toZ Γ (polyNum B v x (succ n₀) q i ρ r))
    (pf := fun r => ZT.toZ Γ (polyNum B v x (dbl (succ n₀)) q (succ (dbl i)) (monus (dbl ρ) q) r))
    (nn_term (succ n₀)) (nn_term (B.denAt (succ (dbl i)) (dbl (succ n₀)) x)) (nn_term q)
    (nn_term (monus (dbl ρ) q)) hqρ hρeq (fun _ => rfl) (Xn_succ (Γ := Γ) B v i (succ n₀) x)
    (fun r => fine_step (succ (dbl i)) r) hq₂ hD'
    (fun r => toZ_polyNum B v x (succ n₀) q i ρ r)
    (fun r => by rw [toZ_polyNum, mk_dbl]) h₁ h₂ k
  -- the convex combination of `u_{2i+1}` and `u_{2i+2}` is bounded by `u_{2i+2}`
  have hmono : Nonneg Γ (𝔞 (maj (succ (succ (dbl i))) ![dbl (succ n₀), K, Hc K L U] *
      (polyDen B dv x (succ n₀) q i * polyDen B dv x (dbl (succ n₀)) q (succ (dbl i)))) -
      𝔞 q * ((𝔞 q - 𝔞 ρ) * (2 * 𝔞 (succ n₀) * 𝔞 (B.denAt (succ (dbl i)) (dbl (succ n₀)) x)) *
          (𝔞 (dbl (succ n₀)) * 𝔞 (maj (succ (dbl i)) ![dbl (succ n₀), K, Hc K L U] *
            (dbl (succ n₀) * B.denAt i (succ n₀) x * Xd B dv i (succ n₀) x *
              Xd B dv (succ (dbl i)) (dbl (succ n₀)) x))) +
        𝔞 (monus (dbl ρ) q) * (𝔞 (maj (succ (succ (dbl i))) ![dbl (succ n₀), K, Hc K L U]) *
          (𝔞 (Xd B dv (succ i) (succ n₀) x) * 𝔞 (Xd B dv (succ (succ (dbl i))) (dbl (succ n₀)) x))))) := by
    have hz : Nonneg Γ (𝔞 q * 𝔞 (B.denAt (succ (dbl i)) (dbl (succ n₀)) x) * 𝔞 (B.denAt i (succ n₀) x) *
        𝔞 (Xd B dv i (succ n₀) x) * 𝔞 (Xd B dv (succ (dbl i)) (dbl (succ n₀)) x) * (2 * 𝔞 (succ n₀)) *
        𝔞 (succ n₀) * 2 * (𝔞 q - 𝔞 ρ) *
        (𝔞 K * 𝔞 (maj (succ (dbl i)) ![dbl (succ n₀), K, Hc K L U]) +
          𝔞 (pw (dbl (succ n₀)) (succ (succ (dbl i)))) * 𝔞 (Hc K L U))) := by
      ipra_nonneg
    refine Cone.of_eq hz ?_
    simp only [Q.mk_mul, map_mul]
    rw [mk_polyDen, mk_polyDen, u2, hq₂, hD', hρeq, mk_dbl]
    ring
  have hfin : Γ ⊢[PRAAx] le (pw (dbl (succ n₀)) (succ (succ (succ (succ (dbl i))))) *
      abs (cellCross B v dv x (succ n₀) q i ρ (dbl (succ n₀)) (succ (dbl i)) (monus (dbl ρ) q) k))
      (maj (succ (succ (dbl i))) ![dbl (succ n₀), K, Hc K L U] *
        (polyDen B dv x (succ n₀) q i * polyDen B dv x (dbl (succ n₀)) q (succ (dbl i)))) := by
    refine le_abs_of_bd₀ ((R.mono nnCone hmono).congr ?_ rfl)
    rw [toZ_cellCross, mk_polyDen, mk_polyDen, mk_dbl]
  have hN : Γ ⊢[PRAAx] succ (succ (dbl i)) + dbl (monus (succ n₀) (succ i)) ≐ succ (n₀ + succ n₀) := by
    have w := natEq (eq_add_of_le hi)
    show Γ ⊢[PRAAx] succ (succ (i + i)) + (monus (succ n₀) (succ i) + monus (succ n₀) (succ i)) ≐
      succ (n₀ + succ n₀)
    apply deriveNat; ipra_simps; linear_combination (-2 : Groth (Q Γ)) * w
  exact finish (dbl_succ_eq n₀) hN hfin

end Local

/-! ## The interpolation program -/

/-- The numerator of `X_nn(p/q)`: the cell is `⌊nn p / q⌋`. -/
def Pn (B : Kernel d) (v : Fin d → ZT n) (x nn p q : PTm n) (k : Fin d) : ZT n :=
  polyNum B v x nn q (quo (nn * p) q) (rem (nn * p) q) k

/-- The denominator of `X_nn(p/q)`. -/
def Pd (B : Kernel d) (dv x nn p q : PTm n) : PTm n := polyDen B dv x nn q (quo (nn * p) q)

/-- The numerator of `X_nn(p/q) − X_nn'(p/q)`, over `Pd(nn) · Pd(nn')`. -/
def polyCross (B : Kernel d) (v : Fin d → ZT n) (dv x nn nn' p q : PTm n) (k : Fin d) : ZT n :=
  cellCross B v dv x nn q (quo (nn * p) q) (rem (nn * p) q) nn' (quo (nn' * p) q) (rem (nn' * p) q) k

theorem polyCross_eq (B : Kernel d) (v : Fin d → ZT n) (dv x nn nn' p q : PTm n) (k : Fin d) :
    polyCross B v dv x nn nn' p q k =
      Pn B v x nn p q k * ZT.ofNat (Pd B dv x nn' p q) - Pn B v x nn' p q k * ZT.ofNat (Pd B dv x nn p q) :=
  rfl

theorem toZ_polyCross (B : Kernel d) (v : Fin d → ZT n) (dv x nn nn' p q : PTm n) (k : Fin d) :
    ZT.toZ Γ (polyCross B v dv x nn nn' p q k) =
      ZT.toZ Γ (Pn B v x nn p q k) * 𝔞 (Pd B dv x nn' p q) -
        ZT.toZ Γ (Pn B v x nn' p q k) * 𝔞 (Pd B dv x nn p q) :=
  toZ_cellCross B v dv x nn q _ _ nn' _ _ k

/-- Provably equal meshes give equal values of the interpolation program. -/
theorem congr_Pn (B : Kernel d) (v : Fin d → ZT n) (x p q : PTm n) {nn nn' : PTm n} (k : Fin d)
    (hn : Γ ⊢[PRAAx] nn ≐ nn') : ZT.toZ Γ (Pn B v x nn p q k) = ZT.toZ Γ (Pn B v x nn' p q k) :=
  congr_polyNum B v x q k hn (congrAp2 quoF (congrMul hn (.eqRefl p)) (.eqRefl q))
    (congrAp2 remF (congrMul hn (.eqRefl p)) (.eqRefl q))

theorem congr_Pd (B : Kernel d) (dv x p q : PTm n) {nn nn' : PTm n} (hn : Γ ⊢[PRAAx] nn ≐ nn') :
    (𝔞 (Pd B dv x nn p q) : Groth (Q Γ)) = 𝔞 (Pd B dv x nn' p q) :=
  congr_polyDen B dv x q hn (congrAp2 quoF (congrMul hn (.eqRefl p)) (.eqRefl q))

theorem subst_polyNum {m : ℕ} (σ : Fin n → PTm m) (B : Kernel d) (v : Fin d → ZT n) (x nn q i ρ : PTm n)
    (k : Fin d) :
    (polyNum B v x nn q i ρ k).subst σ =
      polyNum B (fun l => (v l).subst σ) (Syn.subst σ x) (Syn.subst σ nn) (Syn.subst σ q) (Syn.subst σ i)
        (Syn.subst σ ρ) k := by
  simp only [polyNum, ZT.subst_add, ZT.subst_mul, ZT.subst_ofNat, PTm.subst_mul, Kernel.subst_denAt,
    Kernel.subst_numAt, subst_Xn, subst_sumFin]

theorem subst_polyDen {m : ℕ} (σ : Fin n → PTm m) (B : Kernel d) (dv x nn q i : PTm n) :
    Syn.subst σ (polyDen B dv x nn q i) =
      polyDen B (Syn.subst σ dv) (Syn.subst σ x) (Syn.subst σ nn) (Syn.subst σ q) (Syn.subst σ i) := by
  simp only [polyDen, PTm.subst_mul, Kernel.subst_denAt, subst_Xd]

@[simp] theorem subst_Pd {m : ℕ} (σ : Fin n → PTm m) (B : Kernel d) (dv x nn p q : PTm n) :
    Syn.subst σ (Pd B dv x nn p q) =
      Pd B (Syn.subst σ dv) (Syn.subst σ x) (Syn.subst σ nn) (Syn.subst σ p) (Syn.subst σ q) := by
  simp only [Pd, subst_polyDen, subst_ap2, PTm.subst_mul]

@[simp] theorem subst_polyCross {m : ℕ} (σ : Fin n → PTm m) (B : Kernel d) (v : Fin d → ZT n)
    (dv x nn nn' p q : PTm n) (k : Fin d) :
    (polyCross B v dv x nn nn' p q k).subst σ =
      polyCross B (fun l => (v l).subst σ) (Syn.subst σ dv) (Syn.subst σ x) (Syn.subst σ nn) (Syn.subst σ nn')
        (Syn.subst σ p) (Syn.subst σ q) k := by
  simp only [polyCross, cellCross, ZT.subst_sub, ZT.subst_mul, ZT.subst_ofNat, subst_polyNum, subst_polyDen,
    subst_ap2, PTm.subst_mul]

/-- The refinement estimate on the coarse cell `i` with remainder `ρ`: the fine cell and remainder are
identified by the uniqueness of division with remainder, in the cases `ρ = 0`, `0 < 2ρ < q` and `q ≤ 2ρ`. -/
theorem refinement_cell {B : Kernel d} {v : Fin d → ZT n} {dv U K L x n₀ p q' i ρ : PTm n}
    (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L) (hdv : Γ ⊢[PRAAx] lt zero dv)
    (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv)) (hp : Γ ⊢[PRAAx] le p (succ q'))
    (e : Γ ⊢[PRAAx] succ n₀ * p ≐ succ q' * i + ρ) (hρ : Γ ⊢[PRAAx] lt ρ (succ q')) (k : Fin d) :
    Γ ⊢[PRAAx] le (dbl (succ n₀) * abs (cellCross B v dv x (succ n₀) (succ q') i ρ (dbl (succ n₀))
        (quo (dbl (succ n₀) * p) (succ q')) (rem (dbl (succ n₀) * p) (succ q')) k))
      (Cc K L U * (polyDen B dv x (succ n₀) (succ q') i *
        polyDen B dv x (dbl (succ n₀)) (succ q') (quo (dbl (succ n₀) * p) (succ q')))) := by
  have w := natEq e
  have hq : Γ ⊢[PRAAx] le one (succ q') := succ_pos₀ q'
  have hiN : Γ ⊢[PRAAx] le i (succ n₀) := by
    refine Common.mul_cancel_le hq ?_
    ipra_le 𝔞 ρ + 𝔞 (succ n₀) * sl hp with w
  -- the fine dividend in terms of the coarse cell and remainder
  have e2 : Γ ⊢[PRAAx] dbl (succ n₀) * p ≐ succ q' * dbl i + dbl ρ := by
    show Γ ⊢[PRAAx] (succ n₀ + succ n₀) * p ≐ succ q' * (i + i) + (ρ + ρ)
    apply deriveNat; ipra_simps; linear_combination (2 : Groth (Q Γ)) * w
  refine .orE (zero_or_succ ρ) ?_ ?_
  · -- a coarse node
    have h0 : ((ρ ≐ zero) :: Γ) ⊢[PRAAx] ρ ≐ zero := Prf.hyp0
    have hz : ((ρ ≐ zero) :: Γ) ⊢[PRAAx] dbl (succ n₀) * p ≐ succ q' * dbl i + zero :=
      e2.wk.eqTrans (congrAdd (.eqRefl _) ((congrAdd h0 h0).eqTrans (add_zero zero)))
    have du := div_mod_unique hz (zero_lt_succ q')
    exact transfer (local_node hK.wk hL.wk hdv.wk (fun l => (hv l).wk) hiN.wk k) (.eqRefl _) (.eqRefl _)
      (.eqRefl _) h0 (.eqRefl _) (Prf.andE₁ du) (Prf.andE₂ du)
  · -- inside a cell `i < n`
    have h1 : ((ρ ≐ succ (pred ρ)) :: Γ) ⊢[PRAAx] ρ ≐ succ (pred ρ) := Prf.hyp0
    have hi : ((ρ ≐ succ (pred ρ)) :: Γ) ⊢[PRAAx] le (succ i) (succ n₀) := by
      have wp := natEq h1
      have w' := natEq (e.wk (ψ := ρ ≐ succ (pred ρ)))
      have hp' := hp.wk (ψ := ρ ≐ succ (pred ρ))
      have hlt : ((ρ ≐ succ (pred ρ)) :: Γ) ⊢[PRAAx] le (succ (succ q' * i)) (succ q' * succ n₀) := by
        ipra_le 𝔞 (pred ρ) + 𝔞 (succ n₀) * sl hp' with w' + wp
      refine .orE (lt_or_le i (succ n₀)) Prf.hyp0 ?_
      have hNi : (le (succ n₀) i :: (ρ ≐ succ (pred ρ)) :: Γ) ⊢[PRAAx] le (succ n₀) i := Prf.hyp0
      have h' : (le (succ n₀) i :: (ρ ≐ succ (pred ρ)) :: Γ) ⊢[PRAAx]
          le (succ q' * succ n₀) (succ q' * i) := by
        ipra_le 𝔞 (succ q') * sl hNi
      exact le_lt_absurd _ h' hlt.wk
    refine .orE (lt_or_le (dbl ρ) (succ q')) ?_ ?_
    · -- the first half
      have hlt : (lt (dbl ρ) (succ q') :: (ρ ≐ succ (pred ρ)) :: Γ) ⊢[PRAAx] lt (dbl ρ) (succ q') := Prf.hyp0
      have du := div_mod_unique e2.wk.wk hlt
      exact transfer (local_first hK.wk.wk hL.wk.wk hdv.wk.wk (fun l => (hv l).wk.wk) hi.wk (le_of_lt hlt) k)
        (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) (Prf.andE₁ du) (Prf.andE₂ du)
    · -- the second half
      have hge : (le (succ q') (dbl ρ) :: (ρ ≐ succ (pred ρ)) :: Γ) ⊢[PRAAx] le (succ q') (dbl ρ) := Prf.hyp0
      have hρ' : (le (succ q') (dbl ρ) :: (ρ ≐ succ (pred ρ)) :: Γ) ⊢[PRAAx] le (succ ρ) (succ q') :=
        hρ.wk.wk
      have wm := natEq (eq_add_of_le hge)
      rw [mk_dbl] at wm
      have hr : (le (succ q') (dbl ρ) :: (ρ ≐ succ (pred ρ)) :: Γ) ⊢[PRAAx]
          lt (monus (dbl ρ) (succ q')) (succ q') := by
        show _ ⊢[PRAAx] le (succ (monus (dbl ρ) (succ q'))) (succ q')
        ipra_le 2 * sl hρ' + 1 with wm
      have hz : (le (succ q') (dbl ρ) :: (ρ ≐ succ (pred ρ)) :: Γ) ⊢[PRAAx]
          dbl (succ n₀) * p ≐ succ q' * succ (dbl i) + monus (dbl ρ) (succ q') := by
        have w2 := natEq (e2.wk.wk : (le (succ q') (dbl ρ) :: (ρ ≐ succ (pred ρ)) :: Γ) ⊢[PRAAx]
          dbl (succ n₀) * p ≐ succ q' * dbl i + dbl ρ)
        apply deriveNat
        simp only [Q.mk_add, Q.mk_mul, Q.mk_succ, map_add, map_mul, map_one] at w2 wm ⊢
        rw [mk_dbl ρ] at w2
        linear_combination w2 + wm
      have du := div_mod_unique hz hr
      exact transfer (local_second hK.wk.wk hL.wk.wk hdv.wk.wk (fun l => (hv l).wk.wk) hi.wk hge
        (le_trans (le_succ_self ρ) hρ') k) (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (Prf.andE₁ du) (Prf.andE₂ du)

/-- `eq:ode-produced-refine` at every rational point `t = p/q ∈ [0,1]`:
`2n |Pn(n) Pd(2n) − Pn(2n) Pd(n)| ≤ C Pd(n) Pd(2n)`, that is `‖X_n(t) − X_{2n}(t)‖ ≤ C / (2n)`. -/
theorem euler_refinement_at {B : Kernel d} {v : Fin d → ZT n} {dv U K L x n₀ p q' : PTm n}
    (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L) (hdv : Γ ⊢[PRAAx] lt zero dv)
    (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv)) (hp : Γ ⊢[PRAAx] le p (succ q')) (k : Fin d) :
    Γ ⊢[PRAAx] le (dbl (succ n₀) * abs (polyCross B v dv x (succ n₀) (dbl (succ n₀)) p (succ q') k))
      (Cc K L U * (Pd B dv x (succ n₀) p (succ q') * Pd B dv x (dbl (succ n₀)) p (succ q'))) := by
  have dm := div_mod (Γ := Γ) (succ n₀ * p) q'
  exact refinement_cell hK hL hdv hv hp (Prf.andE₁ dm) (Prf.andE₂ dm) k

/-- `eq:ode-produced-refine` at every rational point, for the maximum norm of the numerator vector:
`2n ‖Pn(n) Pd(2n) − Pn(2n) Pd(n)‖ ≤ C Pd(n) Pd(2n)`. -/
theorem euler_refinement_at_norm {B : Kernel d} {v : Fin d → ZT n} {dv U K L x n₀ p q' : PTm n}
    (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L) (hdv : Γ ⊢[PRAAx] lt zero dv)
    (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv)) (hp : Γ ⊢[PRAAx] le p (succ q')) :
    Γ ⊢[PRAAx] le (dbl (succ n₀) * nrm fun k => polyCross B v dv x (succ n₀) (dbl (succ n₀)) p (succ q') k)
      (Cc K L U * (Pd B dv x (succ n₀) p (succ q') * Pd B dv x (dbl (succ n₀)) p (succ q'))) :=
  mul_nrm_le fun k => euler_refinement_at hK hL hdv hv hp k

end LeanProofs.IPRA.Analysis.EulerInterpolation
