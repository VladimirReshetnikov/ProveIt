import IPRADerivations.Analysis.DifferentialEquations.EulerPolygons.EulerNodeBound
import IPRADerivations.Analysis.DifferentialEquations.EulerPolygons.EulerMajorant

/-!
# The refinement estimate of the exact Euler polygons, produced from the program

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/07_ode.tex`, Theorem
`thm:ode-produced-refinement` ("Complete finite refinement estimate"), `eq:ode-produced-refine` at the nodes of
the coarse mesh: "The polygons computed by `eq:exact-euler` satisfy `‖X_n(t) − X_{2n}(t)‖ ≤ C / (2n)`", with
`C = G H`, `H = (L + K²) Y`, `Y = G U`, `G = 3^K` (`eq:ode-constants`).

The error recurrence that `Foundations/OdeRefinement.node_bound` takes as a hypothesis is derived here from the
Euler program of `EulerPolygons/EulerProgram` and the hypotheses `eq:ode-KL` (`KBound`, `LBound`).

* `errNum … i k` is the numerator of the `k`-th component of `X_{n,i} − X_{2n,2i}` over the denominator
  `Xd(i; n) · Xd(2i; 2n)` (`dbl t = t + t` is the fine mesh and the fine index).
* `ref_cell`: one coarse cell. The paper splits the fine index into its parity cases: at an even fine node the
  residual of the coarse polygon vanishes, at an odd one it is `eq:ode-residual-identity`. Both fine steps of the
  cell are `EulerAlgebra.cell_majorant`, fed with the equations of the two programs, the norm bound
  `euler_node_bound` of the coarse node value, the bounds of the three matrices `B(i/n)`, `B(2i/2n)`,
  `B((2i+1)/2n)`, and the Lipschitz hypothesis at the pairs `(i/n, 2i/2n)` (distance `0`) and
  `(i/n, (2i+1)/2n)` (distance `1/2n`).
* `ref_inv`: by quantifier-free induction on the coarse index, `κ^{2i+2} |errNum| ≤ u_{2i} Xd Xd` for `i ≤ n`,
  with `κ = 2n` and the scalar majorant `u` of `EulerPolygons/EulerMajorant`: the produced recurrence
  `eq:ode-produced-recurrence`.
* `euler_refinement`: `2n |errNum| ≤ C Xd(i; n) Xd(2i; 2n)` for `i ≤ n`, i.e.
  `‖X_{n,i} − X_{2n,2i}‖ ≤ C / (2n)`, from `ref_inv` and `EulerMajorant.maj_bound` (the instance of
  `OdeRefinement.node_bound`), through `finish`.
* `ref_odd`, `euler_refinement_odd`: the same estimate at the odd nodes of the fine mesh, where the coarse
  polygon takes its midpoint value (`oddNum`), for `i < n`.
-/

namespace LeanProofs.IPRA.Analysis.EulerRefinement

open_ipra
open LeanProofs.IPRA.Foundations.TupleRecursion LeanProofs.IPRA.Foundations.SignedNorms
  LeanProofs.IPRA.Foundations.SignedCone LeanProofs.IPRA.Analysis.EulerProgram
  LeanProofs.IPRA.Analysis.EulerNodeBound LeanProofs.IPRA.Analysis.EulerMajorant
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')

variable {n d : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Doubling, and the constants -/

/-- `2 t`, as the term `t + t`: the fine mesh and the fine index. -/
def dbl (t : PTm n) : PTm n := t + t

@[simp] theorem subst_dbl {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) :
    Syn.subst σ (dbl t) = dbl (Syn.subst σ t) := by
  simp only [dbl, PTm.subst_add]

theorem mk_dbl (t : PTm n) : (𝔞 (dbl t) : Groth (Q Γ)) = 2 * 𝔞 t := by
  simp only [dbl, Q.mk_add, map_add]; ring

/-- `H = (L + K²) Y` with `Y = G U`, `G = 3^K` (`eq:ode-constants`). -/
def Hc (K L U : PTm n) : PTm n := (L + K * K) * (pw (num 3) K * U)

/-- `C = G H` (`eq:ode-constants`). -/
def Cc (K L U : PTm n) : PTm n := pw (num 3) K * Hc K L U

@[simp] theorem subst_Hc {m : ℕ} (σ : Fin n → PTm m) (K L U : PTm n) :
    Syn.subst σ (Hc K L U) = Hc (Syn.subst σ K) (Syn.subst σ L) (Syn.subst σ U) := by
  simp only [Hc, PTm.subst_mul, PTm.subst_add, subst_ap2, PTm.subst_num]

@[simp] theorem subst_Cc {m : ℕ} (σ : Fin n → PTm m) (K L U : PTm n) :
    Syn.subst σ (Cc K L U) = Cc (Syn.subst σ K) (Syn.subst σ L) (Syn.subst σ U) := by
  simp only [Cc, subst_Hc, PTm.subst_mul, subst_ap2, PTm.subst_num]

theorem mk_Hc (K L U : PTm n) :
    (𝔞 (Hc K L U) : Groth (Q Γ)) = (𝔞 L + 𝔞 K * 𝔞 K) * (𝔞 (pw (num 3) K) * 𝔞 U) := by
  simp only [Hc, Q.mk_mul, Q.mk_add, map_mul, map_add]

theorem subst_vec3 {m : ℕ} (σ : Fin n → PTm m) (a b c : PTm n) :
    (fun j => Syn.subst σ ((![a, b, c] : Fin 3 → PTm n) j)) = ![Syn.subst σ a, Syn.subst σ b, Syn.subst σ c] := by
  funext j; fin_cases j <;> rfl

/-- The step of the majorant for the parameters `(κ, K, H)`. -/
theorem maj_succ₃ (j κ A H : PTm n) :
    Γ ⊢[PRAAx] maj (succ j) ![κ, A, H] ≐ (κ + A) * maj j ![κ, A, H] + pw κ (succ j) * H :=
  maj_succ j ![κ, A, H]

/-! ## The numerator of the refinement error -/

/-- The numerator of the `k`-th component of `X_{n,i} − X_{2n,2i}`, over `Xd(i; n) · Xd(2i; 2n)`. -/
def errNum (B : Kernel d) (v : Fin d → ZT n) (dv x nn i : PTm n) (k : Fin d) : ZT n :=
  Xn B v i nn x k * ZT.ofNat (Xd B dv (dbl i) (dbl nn) x) -
    Xn B v (dbl i) (dbl nn) x k * ZT.ofNat (Xd B dv i nn x)

theorem subst_errNum {m : ℕ} (σ : Fin n → PTm m) (B : Kernel d) (v : Fin d → ZT n) (dv x nn i : PTm n)
    (k : Fin d) :
    (errNum B v dv x nn i k).subst σ =
      errNum B (fun l => (v l).subst σ) (Syn.subst σ dv) (Syn.subst σ x) (Syn.subst σ nn) (Syn.subst σ i) k := by
  simp only [errNum, ZT.subst_sub, ZT.subst_mul, ZT.subst_ofNat, subst_Xn, subst_Xd, subst_dbl]

theorem toZ_errNum (B : Kernel d) (v : Fin d → ZT n) (dv x nn i : PTm n) (k : Fin d) :
    ZT.toZ Γ (errNum B v dv x nn i k) =
      ZT.toZ Γ (Xn B v i nn x k) * 𝔞 (Xd B dv (dbl i) (dbl nn) x) -
        ZT.toZ Γ (Xn B v (dbl i) (dbl nn) x k) * 𝔞 (Xd B dv i nn x) := by
  simp only [errNum, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat]

/-- The numerator of the `k`-th component of `X_n(t) − X_{2n,2i+1}` at the midpoint `t = (2i+1)/2n` of the
coarse cell `i`, where the coarse polygon has the value `(2n b x + M x) / (2n b Xd(i; n))` by interpolation; the
denominator is `2n b Xd(i; n) · Xd(2i+1; 2n)`. -/
def oddNum (B : Kernel d) (v : Fin d → ZT n) (dv x nn i : PTm n) (k : Fin d) : ZT n :=
  (ZT.ofNat (dbl nn * B.denAt i nn x) * Xn B v i nn x k +
      ZT.sumFin fun l => B.numAt k l i nn x * Xn B v i nn x l) *
      ZT.ofNat (Xd B dv (succ (dbl i)) (dbl nn) x) -
    Xn B v (succ (dbl i)) (dbl nn) x k * ZT.ofNat (dbl nn * B.denAt i nn x * Xd B dv i nn x)

theorem toZ_oddNum (B : Kernel d) (v : Fin d → ZT n) (dv x nn i : PTm n) (k : Fin d) :
    ZT.toZ Γ (oddNum B v dv x nn i k) =
      (2 * 𝔞 nn * 𝔞 (B.denAt i nn x) * ZT.toZ Γ (Xn B v i nn x k) +
          ∑ l, ZT.toZ Γ (B.numAt k l i nn x) * ZT.toZ Γ (Xn B v i nn x l)) *
          𝔞 (Xd B dv (succ (dbl i)) (dbl nn) x) -
        ZT.toZ Γ (Xn B v (succ (dbl i)) (dbl nn) x k) *
          (2 * 𝔞 nn * 𝔞 (B.denAt i nn x) * 𝔞 (Xd B dv i nn x)) := by
  simp only [oddNum, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_add, ZT.toZ_ofNat, ZT.toZ_sumFin, Q.mk_mul, map_mul, mk_dbl]

/-- The invariant of the refinement induction: for `i ≤ n`, `κ^{2i+2} |errNum| ≤ u_{2i} Xd(i; n) Xd(2i; 2n)`. -/
def RefInv (B : Kernel d) (v : Fin d → ZT n) (dv U K L x nn i : PTm n) : Fm PTm n :=
  le i nn ⟶ conjFin fun k =>
    le (pw (dbl nn) (succ (succ (dbl i))) * abs (errNum B v dv x nn i k))
      (maj (dbl i) ![dbl nn, K, Hc K L U] * (Xd B dv i nn x * Xd B dv (dbl i) (dbl nn) x))

@[simp] theorem subst_RefInv {m : ℕ} (σ : Fin n → PTm m) (B : Kernel d) (v : Fin d → ZT n)
    (dv U K L x nn i : PTm n) :
    (RefInv B v dv U K L x nn i).subst σ =
      RefInv B (fun l => (v l).subst σ) (Syn.subst σ dv) (Syn.subst σ U) (Syn.subst σ K) (Syn.subst σ L)
        (Syn.subst σ x) (Syn.subst σ nn) (Syn.subst σ i) := by
  simp only [RefInv, Fm.subst_imp, subst_le, subst_conjFin, subst_abs, subst_errNum, subst_maj, subst_vec3,
    subst_Hc, subst_Xd, subst_dbl, PTm.subst_mul, subst_ap2, ConciseIPRA.PTm.subst_succ]

theorem RefInv_QF (B : Kernel d) (v : Fin d → ZT n) (dv U K L x nn i : PTm n) :
    (RefInv B v dv U K L x nn i).QF :=
  ⟨le_QF _ _, conjFin_QF fun _ => le_QF _ _⟩

section Cell

variable {B : Kernel d} {v : Fin d → ZT n} {dv U K L x n₀ i : PTm n}

/-- The base of the refinement induction: the two polygons start from the same vector. -/
theorem ref_base (k : Fin d) :
    Γ ⊢[PRAAx] le (pw (dbl (succ n₀)) (succ (succ (dbl zero))) * abs (errNum B v dv x (succ n₀) zero k))
      (maj (dbl zero) ![dbl (succ n₀), K, Hc K L U] *
        (Xd B dv zero (succ n₀) x * Xd B dv (dbl zero) (dbl (succ n₀)) x)) := by
  have e0 : Γ ⊢[PRAAx] dbl (zero : PTm n) ≐ zero := add_zero zero
  have cX := congrXn (Γ := Γ) B v x k e0 (.eqRefl (dbl (succ n₀)))
  have cD := natEq (congrXd (Γ := Γ) B dv x e0 (.eqRefl (dbl (succ n₀))))
  refine le_abs_of_bd₀ ((Bd.zero (nn_term _)).congr ?_ rfl)
  rw [toZ_errNum, cX, cD, Xn_zero, Xn_zero, Xd_zero, Xd_zero]
  ring

/-- One coarse cell of the refinement induction: the produced recurrence `eq:ode-produced-recurrence` over two
fine steps, the first to the midpoint of the cell (the residual vanishes), the second with the residual
`eq:ode-residual-identity`. -/
theorem ref_cell (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L) (hdv : Γ ⊢[PRAAx] lt zero dv)
    (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv)) (hi : Γ ⊢[PRAAx] le (succ i) (succ n₀))
    (ih : ∀ k, Γ ⊢[PRAAx] le (pw (dbl (succ n₀)) (succ (succ (dbl i))) * abs (errNum B v dv x (succ n₀) i k))
      (maj (dbl i) ![dbl (succ n₀), K, Hc K L U] *
        (Xd B dv i (succ n₀) x * Xd B dv (dbl i) (dbl (succ n₀)) x))) :
    (∀ k, Γ ⊢[PRAAx] le (pw (dbl (succ n₀)) (succ (succ (succ (dbl i)))) *
        abs (oddNum B v dv x (succ n₀) i k))
      (maj (succ (dbl i)) ![dbl (succ n₀), K, Hc K L U] *
        (dbl (succ n₀) * B.denAt i (succ n₀) x * Xd B dv i (succ n₀) x *
          Xd B dv (succ (dbl i)) (dbl (succ n₀)) x))) ∧
    ∀ k, Γ ⊢[PRAAx] le (pw (dbl (succ n₀)) (succ (succ (dbl (succ i)))) *
        abs (errNum B v dv x (succ n₀) (succ i) k))
      (maj (dbl (succ i)) ![dbl (succ n₀), K, Hc K L U] *
        (Xd B dv (succ i) (succ n₀) x * Xd B dv (dbl (succ i)) (dbl (succ n₀)) x)) := by
  -- the arguments are in the interval
  have hin : Γ ⊢[PRAAx] le i (succ n₀) := le_trans (le_succ_self i) hi
  have hnn : Γ ⊢[PRAAx] lt zero (succ n₀) := succ_pos₀ n₀
  have hκ : Γ ⊢[PRAAx] lt zero (dbl (succ n₀)) := by
    show Γ ⊢[PRAAx] le (succ zero) (succ n₀ + succ n₀)
    ipra_le 𝔞 n₀ + 𝔞 (succ n₀)
  have h2i : Γ ⊢[PRAAx] le (dbl i) (dbl (succ n₀)) := by
    show Γ ⊢[PRAAx] le (i + i) (succ n₀ + succ n₀)
    ipra_le sl hin + sl hin
  have h2i1 : Γ ⊢[PRAAx] le (succ (dbl i)) (dbl (succ n₀)) := by
    show Γ ⊢[PRAAx] le (succ (i + i)) (succ n₀ + succ n₀)
    ipra_le sl hi + sl hi + 1
  obtain ⟨-, hrow⟩ := kbound_use hK hnn hin
  obtain ⟨-, hrow₀⟩ := kbound_use hK hκ h2i
  obtain ⟨-, hrow₁⟩ := kbound_use hK hκ h2i1
  -- the Lipschitz hypothesis at the same point `i/n = 2i/2n`
  have hl₀ : ∀ r, Γ ⊢[PRAAx] le (rowSum (B.cross i (succ n₀) (dbl i) (dbl (succ n₀)) x) r) zero := fun r => by
    have h := lbound_use hL hnn hin hκ h2i r
    have e : Γ ⊢[PRAAx] i * dbl (succ n₀) ≐ dbl i * succ n₀ := by
      show Γ ⊢[PRAAx] i * (succ n₀ + succ n₀) ≐ (i + i) * succ n₀
      ipra_ring
    have z1 := natEq ((congrMonus e (.eqRefl (dbl i * succ n₀))).eqTrans (monus_self _))
    have z2 := natEq ((congrMonus (.eqRefl (dbl i * succ n₀)) e).eqTrans (monus_self _))
    have hc : Γ ⊢[PRAAx] le one (succ n₀ * dbl (succ n₀)) := mul_pos₀ hnn hκ
    refine Common.mul_cancel_le hc ?_
    ipra_le sl h using (rw [z1, z2]; ring)
  -- the Lipschitz hypothesis at the distance `1/2n`
  have hl₁ : ∀ r, Γ ⊢[PRAAx] le (dbl (succ n₀) * rowSum (B.cross i (succ n₀) (succ (dbl i)) (dbl (succ n₀)) x) r)
      (L * B.denAt i (succ n₀) x * B.denAt (succ (dbl i)) (dbl (succ n₀)) x) := fun r => by
    have h := lbound_use hL hnn hin hκ h2i1 r
    have e : Γ ⊢[PRAAx] succ (dbl i) * succ n₀ ≐ i * dbl (succ n₀) + succ n₀ := by
      show Γ ⊢[PRAAx] succ (i + i) * succ n₀ ≐ i * (succ n₀ + succ n₀) + succ n₀
      ipra_ring
    have z1 := natEq ((congrMonus (.eqRefl (i * dbl (succ n₀))) e).eqTrans (monus_add _ _))
    have z2 := natEq ((congrMonus e (.eqRefl (i * dbl (succ n₀)))).eqTrans (add_monus' _ _))
    have hc : Γ ⊢[PRAAx] le one (succ n₀) := hnn
    refine Common.mul_cancel_le hc ?_
    ipra_le sl h using (rw [z1, z2]; ring)
  -- the three matrices and their two differences
  have hM : RowBd (Nonneg Γ) (fun r l => ZT.toZ Γ (B.numAt r l i (succ n₀) x))
      (𝔞 K * 𝔞 (B.denAt i (succ n₀) x)) :=
    rowBd_congr (rowBd_of_le₁ hrow) (fun _ _ => rfl) (by simp only [Q.mk_mul, map_mul])
  have hM₀ : RowBd (Nonneg Γ) (fun r l => ZT.toZ Γ (B.numAt r l (dbl i) (dbl (succ n₀)) x))
      (𝔞 K * 𝔞 (B.denAt (dbl i) (dbl (succ n₀)) x)) :=
    rowBd_congr (rowBd_of_le₁ hrow₀) (fun _ _ => rfl) (by simp only [Q.mk_mul, map_mul])
  have hM₁ : RowBd (Nonneg Γ) (fun r l => ZT.toZ Γ (B.numAt r l (succ (dbl i)) (dbl (succ n₀)) x))
      (𝔞 K * 𝔞 (B.denAt (succ (dbl i)) (dbl (succ n₀)) x)) :=
    rowBd_congr (rowBd_of_le₁ hrow₁) (fun _ _ => rfl) (by simp only [Q.mk_mul, map_mul])
  have hL₀ : RowBd (Nonneg Γ) (fun r l =>
      𝔞 (B.denAt (dbl i) (dbl (succ n₀)) x) * ZT.toZ Γ (B.numAt r l i (succ n₀) x) -
        𝔞 (B.denAt i (succ n₀) x) * ZT.toZ Γ (B.numAt r l (dbl i) (dbl (succ n₀)) x)) 0 :=
    rowBd_congr (rowBd_of_le₁ hl₀)
      (fun _ _ => by simp only [Kernel.cross, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat])
      (by simp only [Q.mk_zero, map_zero])
  have hL₁ : RowBd (Nonneg Γ) (fun r l => 2 * 𝔞 (succ n₀) *
      (𝔞 (B.denAt (succ (dbl i)) (dbl (succ n₀)) x) * ZT.toZ Γ (B.numAt r l i (succ n₀) x) -
        𝔞 (B.denAt i (succ n₀) x) * ZT.toZ Γ (B.numAt r l (succ (dbl i)) (dbl (succ n₀)) x)))
      (𝔞 L * 𝔞 (B.denAt i (succ n₀) x) * 𝔞 (B.denAt (succ (dbl i)) (dbl (succ n₀)) x)) :=
    rowBd_congr (rowBd_of_le hl₁)
      (fun _ _ => by rw [mk_dbl]; simp only [Kernel.cross, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat])
      (by simp only [Q.mk_mul, map_mul])
  -- the equations of the two programs
  have e2 : (𝔞 (dbl (succ n₀)) : Groth (Q Γ)) = 2 * 𝔞 (succ n₀) := mk_dbl _
  have hx' := Xn_succ (Γ := Γ) B v i (succ n₀) x
  have hw₁ : ∀ r, ZT.toZ Γ (Xn B v (succ (dbl i)) (dbl (succ n₀)) x r) =
      2 * 𝔞 (succ n₀) * 𝔞 (B.denAt (dbl i) (dbl (succ n₀)) x) * ZT.toZ Γ (Xn B v (dbl i) (dbl (succ n₀)) x r) +
        ∑ l, ZT.toZ Γ (B.numAt r l (dbl i) (dbl (succ n₀)) x) *
          ZT.toZ Γ (Xn B v (dbl i) (dbl (succ n₀)) x l) := fun r => by
    rw [Xn_succ (Γ := Γ) B v (dbl i) (dbl (succ n₀)) x r, e2]
  have hw₂ : ∀ r, ZT.toZ Γ (Xn B v (succ (succ (dbl i))) (dbl (succ n₀)) x r) =
      2 * 𝔞 (succ n₀) * 𝔞 (B.denAt (succ (dbl i)) (dbl (succ n₀)) x) *
          ZT.toZ Γ (Xn B v (succ (dbl i)) (dbl (succ n₀)) x r) +
        ∑ l, ZT.toZ Γ (B.numAt r l (succ (dbl i)) (dbl (succ n₀)) x) *
          ZT.toZ Γ (Xn B v (succ (dbl i)) (dbl (succ n₀)) x l) := fun r => by
    rw [Xn_succ (Γ := Γ) B v (succ (dbl i)) (dbl (succ n₀)) x r, e2]
  have hq₁ : (𝔞 (Xd B dv (succ (dbl i)) (dbl (succ n₀)) x) : Groth (Q Γ)) =
      2 * 𝔞 (succ n₀) * 𝔞 (B.denAt (dbl i) (dbl (succ n₀)) x) * 𝔞 (Xd B dv (dbl i) (dbl (succ n₀)) x) := by
    rw [Xd_succ (Γ := Γ) B dv (dbl i) (dbl (succ n₀)) x, e2]
  have hq₂ : (𝔞 (Xd B dv (succ (succ (dbl i))) (dbl (succ n₀)) x) : Groth (Q Γ)) =
      2 * 𝔞 (succ n₀) * 𝔞 (B.denAt (succ (dbl i)) (dbl (succ n₀)) x) *
        𝔞 (Xd B dv (succ (dbl i)) (dbl (succ n₀)) x) := by
    rw [Xd_succ (Γ := Γ) B dv (succ (dbl i)) (dbl (succ n₀)) x, e2]
  have hD' := Xd_succ (Γ := Γ) B dv i (succ n₀) x
  -- the bound of the coarse node value and the induction hypothesis
  have hx : ∀ r, Bd (Nonneg Γ) (ZT.toZ Γ (Xn B v i (succ n₀) x r))
      (𝔞 (pw (num 3) K) * 𝔞 U * 𝔞 (Xd B dv i (succ n₀) x)) := fun r =>
    (bd_of_le₁ (euler_node_bound hK hdv hv hin r)).congr rfl (by simp only [Q.mk_mul, map_mul])
  have pk := natEq (pw_succ (Γ := Γ) (dbl (succ n₀)) (succ (dbl i)))
  simp only [Q.mk_mul, map_mul] at pk
  have he : ∀ r, Bd (Nonneg Γ) (2 * 𝔞 (succ n₀) * 𝔞 (pw (dbl (succ n₀)) (succ (dbl i))) *
      (ZT.toZ Γ (Xn B v i (succ n₀) x r) * 𝔞 (Xd B dv (dbl i) (dbl (succ n₀)) x) -
        ZT.toZ Γ (Xn B v (dbl i) (dbl (succ n₀)) x r) * 𝔞 (Xd B dv i (succ n₀) x)))
      (𝔞 (maj (dbl i) ![dbl (succ n₀), K, Hc K L U]) *
        (𝔞 (Xd B dv i (succ n₀) x) * 𝔞 (Xd B dv (dbl i) (dbl (succ n₀)) x))) := fun r =>
    (bd_of_le (ih r)).congr (by rw [toZ_errNum, pk, e2]; ring) (by simp only [Q.mk_mul, map_mul])
  -- the two fine steps of the cell
  obtain ⟨hod, hev⟩ := EulerAlgebra.cell_majorant (P := Nonneg Γ) nnCone
    (ν := 𝔞 (succ n₀)) (β := 𝔞 (B.denAt i (succ n₀) x)) (c₀ := 𝔞 (B.denAt (dbl i) (dbl (succ n₀)) x))
    (c₁ := 𝔞 (B.denAt (succ (dbl i)) (dbl (succ n₀)) x)) (K := 𝔞 K) (L := 𝔞 L)
    (q₀ := 𝔞 (Xd B dv (dbl i) (dbl (succ n₀)) x)) (D := 𝔞 (Xd B dv i (succ n₀) x))
    (p := 𝔞 (pw (dbl (succ n₀)) (succ (dbl i)))) (u := 𝔞 (maj (dbl i) ![dbl (succ n₀), K, Hc K L U]))
    (Y := 𝔞 (pw (num 3) K) * 𝔞 U)
    (y := fun r => 2 * 𝔞 (succ n₀) * 𝔞 (B.denAt i (succ n₀) x) * ZT.toZ Γ (Xn B v i (succ n₀) x r) +
      ∑ l, ZT.toZ Γ (B.numAt r l i (succ n₀) x) * ZT.toZ Γ (Xn B v i (succ n₀) x l))
    (nn_term _) (nn_term _) (nn_term _) (nn_term _) (nn_term _) (nn_term _) (nn_term _) (nn_term _)
    (nn_term _) (nn_term _) (nn_mul (nn_term _) (nn_term _))
    hM hM₀ hM₁ hL₀ hL₁ (fun _ => rfl) hx' hw₁ hw₂ hq₁ hq₂ hD' hx he
  -- back to the terms at the midpoint and at the next coarse node
  have ej : Γ ⊢[PRAAx] dbl (succ i) ≐ succ (succ (dbl i)) := by
    show Γ ⊢[PRAAx] succ i + succ i ≐ succ (succ (i + i))
    ipra_ring
  have cD := natEq (congrXd (Γ := Γ) B dv x ej (.eqRefl (dbl (succ n₀))))
  have pk3 := natEq (pw_succ (Γ := Γ) (dbl (succ n₀)) (succ (succ (dbl i))))
  have pk4 := natEq ((congrAp2 powF (congrSucc (congrSucc ej)) (.eqRefl (dbl (succ n₀)))).eqTrans
    (pw_succ (Γ := Γ) (dbl (succ n₀)) (succ (succ (succ (dbl i))))))
  have u1 := natEq (maj_succ₃ (Γ := Γ) (dbl i) (dbl (succ n₀)) K (Hc K L U))
  have u2 := natEq (maj_succ₃ (Γ := Γ) (succ (dbl i)) (dbl (succ n₀)) K (Hc K L U))
  have cU := natEq (congrMaj (Γ := Γ) (ps := ![dbl (succ n₀), K, Hc K L U]) ej fun _ => .eqRefl _)
  simp only [Q.mk_mul, Q.mk_add, map_mul, map_add] at pk3 pk4 u1 u2
  refine ⟨fun k => le_abs_of_bd₀ ((hod k).congr ?_ ?_), fun k => le_abs_of_bd₀ ((hev k).congr ?_ ?_)⟩
  · rw [toZ_oddNum, pk3, pk, e2]; ring
  · simp only [Q.mk_mul, map_mul]
    rw [u1, mk_Hc, e2]
  · have cX := congrXn (Γ := Γ) B v x k ej (.eqRefl (dbl (succ n₀)))
    rw [toZ_errNum, cX, cD, pk4, pk3, pk, e2]; ring
  · simp only [Q.mk_mul, map_mul]
    rw [cD, cU, u2, u1, pk, mk_Hc, e2]; ring

end Cell

/-- The produced recurrence `eq:ode-produced-recurrence`, iterated: for `i ≤ n`,
`κ^{2i+2} |errNum_i| ≤ u_{2i} Xd(i; n) Xd(2i; 2n)`. -/
theorem ref_inv {B : Kernel d} {v : Fin d → ZT n} {dv U K L x : PTm n} (n₀ : PTm n)
    (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L) (hdv : Γ ⊢[PRAAx] lt zero dv)
    (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv)) (i : PTm n) :
    Γ ⊢[PRAAx] RefInv B v dv U K L x (succ n₀) i := by
  have hvs : ∀ l, Γ.map Fm.shift ⊢[PRAAx] le (abs (zshift (v l))) (Syn.shift U * Syn.shift dv) := fun l => by
    have a := (hv l).shift
    simp only [Fm.shift, subst_le, subst_abs, PTm.subst_mul] at a
    exact a
  have hdvs : Γ.map Fm.shift ⊢[PRAAx] lt zero (Syn.shift dv) := by
    have a := hdv.shift
    simp only [Fm.shift, subst_lt, ConciseIPRA.PTm.subst_zero] at a
    exact a
  have hall : Γ ⊢[PRAAx] Fm.all (RefInv B (fun l => zshift (v l)) (Syn.shift dv) (Syn.shift U) (Syn.shift K)
      (Syn.shift L) (Syn.shift x) (succ (Syn.shift n₀)) (var 0)) := by
    ipra_qfind (RefInv_QF _ _ _ _ _ _ _ _ _) [subst_RefInv, zshift_inst, zshift_repl]
    · exact .impI (conjFin_intro fun k => ref_base k)
    · refine .impI ?_
      have hj : (le (succ (var 0)) (succ (Syn.shift n₀)) ::
          RefInv B (fun l => zshift (v l)) (Syn.shift dv) (Syn.shift U) (Syn.shift K) (Syn.shift L)
            (Syn.shift x) (succ (Syn.shift n₀)) (var 0) :: Γ.map Fm.shift) ⊢[PRAAx]
          le (succ (var 0)) (succ (Syn.shift n₀)) := Prf.hyp0
      have ih := Prf.impE (φ := le (var 0) (succ (Syn.shift n₀))) Prf.hyp1 (le_trans (le_succ_self _) hj)
      exact conjFin_intro
        (ref_cell (kbound_shift hK).wk.wk (lbound_shift hL).wk.wk hdvs.wk.wk (fun l => (hvs l).wk.wk) hj
          (conjFin_elim ih)).2
  have h := Prf.allE i hall
  simp only [subst_RefInv, zshift_inst, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero,
    ConciseIPRA.PTm.subst_succ] at h
  exact h

/-- The refinement error at the midpoint of the coarse cell `i < n`:
`κ^{2i+3} |oddNum| ≤ u_{2i+1} (2n b Xd(i; n)) Xd(2i+1; 2n)`. -/
theorem ref_odd {B : Kernel d} {v : Fin d → ZT n} {dv U K L x n₀ i : PTm n}
    (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L) (hdv : Γ ⊢[PRAAx] lt zero dv)
    (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv)) (hi : Γ ⊢[PRAAx] le (succ i) (succ n₀)) (k : Fin d) :
    Γ ⊢[PRAAx] le (pw (dbl (succ n₀)) (succ (succ (succ (dbl i)))) * abs (oddNum B v dv x (succ n₀) i k))
      (maj (succ (dbl i)) ![dbl (succ n₀), K, Hc K L U] *
        (dbl (succ n₀) * B.denAt i (succ n₀) x * Xd B dv i (succ n₀) x *
          Xd B dv (succ (dbl i)) (dbl (succ n₀)) x)) :=
  (ref_cell hK hL hdv hv hi
    (conjFin_elim (Prf.impE (ref_inv n₀ hK hL hdv hv i) (le_trans (le_succ_self i) hi)))).1 k

/-- From the majorant to the constant `C`: if `κ^{N+2} err ≤ u_N DD` with `N ≤ κ = k₀ + 1`, then
`κ err ≤ C DD`, by `EulerMajorant.maj_bound` (the instance of `OdeRefinement.node_bound`). -/
theorem finish {κ k₀ K L U N dd err DD : PTm n} (hκ : Γ ⊢[PRAAx] κ ≐ succ k₀)
    (hN : Γ ⊢[PRAAx] N + dd ≐ succ k₀)
    (h : Γ ⊢[PRAAx] le (pw κ (succ (succ N)) * err) (maj N ![κ, K, Hc K L U] * DD)) :
    Γ ⊢[PRAAx] le (κ * err) (Cc K L U * DD) := by
  have mb := maj_bound (A := K) (H := Hc K L U) hκ hN
  have p1 := natEq (pw_succ (Γ := Γ) κ (succ N))
  have p2 := natEq (pw_succ (Γ := Γ) κ N)
  have kk := natEq hκ
  have eC : (𝔞 (Cc K L U) : Groth (Q Γ)) = 𝔞 (pw (num 3) K) * 𝔞 (Hc K L U) := by
    simp only [Cc, Q.mk_mul, map_mul]
  have hpw : Γ ⊢[PRAAx] lt zero (pw κ N) :=
    le_congr (.eqRefl _) (pw_pos' (Common.pos_of_succ hκ) N).eqSymm (succ_pos₀ _)
  have hκp : Γ ⊢[PRAAx] lt zero κ := le_congr (.eqRefl _) hκ.eqSymm (succ_pos₀ _)
  have hc : Γ ⊢[PRAAx] le one (pw κ N * κ) := mul_pos₀ hpw hκp
  refine Common.mul_cancel_le hc ?_
  ipra_le sl h + sl mb * 𝔞 DD using
    (rw [eC, p1, p2]
     linear_combination (𝔞 (pw (num 3) K) * 𝔞 (pw κ N) * 𝔞 (Hc K L U) * 𝔞 DD) * kk)

section Estimates

variable {B : Kernel d} {v : Fin d → ZT n} {dv U K L x n₀ i : PTm n}

theorem dbl_succ_eq (n₀ : PTm n) : Γ ⊢[PRAAx] dbl (succ n₀) ≐ succ (n₀ + succ n₀) := by
  show Γ ⊢[PRAAx] succ n₀ + succ n₀ ≐ succ (n₀ + succ n₀)
  ipra_ring

/-- `eq:ode-produced-refine` at the nodes of the coarse mesh: for `i ≤ n`,
`2n |errNum_i| ≤ C Xd(i; n) Xd(2i; 2n)`, that is `‖X_{n,i} − X_{2n,2i}‖ ≤ C / (2n)`. -/
theorem euler_refinement (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L)
    (hdv : Γ ⊢[PRAAx] lt zero dv) (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv))
    (hi : Γ ⊢[PRAAx] le i (succ n₀)) (k : Fin d) :
    Γ ⊢[PRAAx] le (dbl (succ n₀) * abs (errNum B v dv x (succ n₀) i k))
      (Cc K L U * (Xd B dv i (succ n₀) x * Xd B dv (dbl i) (dbl (succ n₀)) x)) := by
  have h := conjFin_elim (Prf.impE (ref_inv n₀ hK hL hdv hv i) hi) k
  have hN : Γ ⊢[PRAAx] dbl i + dbl (monus (succ n₀) i) ≐ succ (n₀ + succ n₀) := by
    have w := natEq (eq_add_of_le hi)
    show Γ ⊢[PRAAx] (i + i) + (monus (succ n₀) i + monus (succ n₀) i) ≐ succ (n₀ + succ n₀)
    apply deriveNat; ipra_simps; linear_combination (-2 : Groth (Q Γ)) * w
  exact finish (dbl_succ_eq n₀) hN h

/-- `eq:ode-produced-refine` at the midpoint of the coarse cell `i < n` (an odd node of the fine mesh):
`2n |oddNum_i| ≤ C (2n b Xd(i; n)) Xd(2i+1; 2n)`. -/
theorem euler_refinement_odd (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L)
    (hdv : Γ ⊢[PRAAx] lt zero dv) (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv))
    (hi : Γ ⊢[PRAAx] le (succ i) (succ n₀)) (k : Fin d) :
    Γ ⊢[PRAAx] le (dbl (succ n₀) * abs (oddNum B v dv x (succ n₀) i k))
      (Cc K L U * (dbl (succ n₀) * B.denAt i (succ n₀) x * Xd B dv i (succ n₀) x *
        Xd B dv (succ (dbl i)) (dbl (succ n₀)) x)) := by
  have h := ref_odd hK hL hdv hv hi k
  have hN : Γ ⊢[PRAAx] succ (dbl i) + succ (dbl (monus (succ n₀) (succ i))) ≐ succ (n₀ + succ n₀) := by
    have w := natEq (eq_add_of_le hi)
    show Γ ⊢[PRAAx] succ (i + i) + succ (monus (succ n₀) (succ i) + monus (succ n₀) (succ i)) ≐
      succ (n₀ + succ n₀)
    apply deriveNat; ipra_simps; linear_combination (-2 : Groth (Q Γ)) * w
  exact finish (dbl_succ_eq n₀) hN h

end Estimates

end LeanProofs.IPRA.Analysis.EulerRefinement
