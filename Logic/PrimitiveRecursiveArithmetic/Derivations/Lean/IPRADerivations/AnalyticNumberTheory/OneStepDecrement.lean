import IPRADerivations.AnalyticNumberTheory.OneStepRaw
import IPRADerivations.Core.Header

/-!
# The one-step decrement (`pnt_ipra_constructive_2026-11-14`, Lemma `con:one-step`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, Lemma `con:one-step`:
"`|r(u)| ≤ a` for `s ≤ u ≤ t` … then `|r(t)| ≤ a − 3δ`." Discretely, at denominator `D` (`a = A/D`, `δ = 1/D`):
the stage bound `D|ψ(m) − Fm| ≤ AFm` for `Y ≤ m ≤ x` gives (`one_step_decrement`)

  `D |ψ(x) − Fx| + 3Fx ≤ AFx`,

the stage bound at `x` with `A − 3`, once the integer condition `DecC` on the dyadic exponents holds. The
logarithms are harmonic (`u_m = S(Km) − S(K)`) and enter only through powers of two:

* `u_pow`, `u_shift`, `u_low`: `u_{2^T} ≤ TF`, `u_{N 2^T} ≤ u_N + TF`, `μF ≤ 2u_{2^μ} + F` when `2K2^μ ≤ F`
  (`HarmonicLogPow2.S_pow2`, `Doubling.S_pow2_lower`);
* `decrement_alg`: the arithmetic over opaque terms, a slack certificate (checked by elimination) followed by
  cancellation of `48 D Z u_x²`. With `x ≤ 2^T`, `x ≤ N 2^{σ+1}`, blocks `2^μ < d ≤ 2^μ 2^{2hB} ≤ N` and
  `Z ≤ 2^σ, 2^μ`, the condition is

  `Z(2W + 3A²B) + 400ADBT ≤ 3ZA²Bμ`,
  `W = 72DT² + 48DA + 192D²T(σ+1) + 192D² + 24D²(19222T + 11070)`:

  the deficit gain `3A²B(μ − 1)` of the `B` blocks beats the cost `72DT²` of the decrement, the cost `192D²T(σ+1)`
  of the unknown region `m < Y` (con:global), the Selberg remainders and the block errors.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.OneStepDecrement

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono wt)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogPow2 (S_pow2)
open LeanProofs.IPRA.AnalyticNumberTheory.Doubling (S_pow2_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockChain (one_le_pw' u_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockTests (one_le_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockDeficit (OnBlock stg)
open LeanProofs.IPRA.AnalyticNumberTheory.ContractionSplit (Stage)
open LeanProofs.IPRA.AnalyticNumberTheory.OneStepRaw (one_step_raw)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedBound (psiB qB inst2_psiB inst2_qB)
open LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum (Q4)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd scale_absd)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le cancel_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryPointwise (quo_mul_le)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Harmonic logarithms of powers of two -/

theorem monus_le_of {X Z0 c : PTm n} (h : Γ ⊢[PRAAx] le X (Z0 + c)) (hX : Γ ⊢[PRAAx] le Z0 X) :
    Γ ⊢[PRAAx] le (monus X Z0) c := by
  have e := natEq (eq_add_of_le hX)
  ipra_le sl h with e

theorem monus_bound {X Y Z0 c : PTm n} (h : Γ ⊢[PRAAx] le X (Y + c)) (hX : Γ ⊢[PRAAx] le Z0 X)
    (hY : Γ ⊢[PRAAx] le Z0 Y) : Γ ⊢[PRAAx] le (monus X Z0) (monus Y Z0 + c) := by
  have e1 := natEq (eq_add_of_le hX)
  have e2 := natEq (eq_add_of_le hY)
  ipra_le sl h with e1 - e2

/-- `u_{2^T} ≤ TF`. -/
theorem u_pow (K F T : PTm n) : Γ ⊢[PRAAx] le (U (pw two T) K F) (T * F) := by
  have hKT : Γ ⊢[PRAAx] le K (K * pw two T) := by
    have p := le_scale K (one_le_pw' (le_succ_self (Γ := Γ) one) T)
    ipra_le sl p
  exact monus_le_of (S_pow2 K F T) (S_mono F hKT)

/-- `u_{N 2^T} ≤ u_N + TF`. -/
theorem u_shift {K N : PTm n} (F T : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le (U (N * pw two T) K F) (U N K F + T * F) := by
  have e : Γ ⊢[PRAAx] K * (N * pw two T) ≐ K * N * pw two T := by ipra_ring
  have p := le_congr (congrAp2 (sumF hB) e (.eqRefl F)).eqSymm (.eqRefl _) (S_pow2 (K * N) F T)
  have hKN : Γ ⊢[PRAAx] le K (K * N) := by
    have q := le_scale K hN
    ipra_le sl q
  have hNT : Γ ⊢[PRAAx] le (K * N) (K * (N * pw two T)) := by
    have q := le_scale (K * N) (one_le_pw' (le_succ_self (Γ := Γ) one) T)
    ipra_le sl q
  exact monus_bound p (S_mono F (le_trans hKN hNT)) (S_mono F hKN)

/-- `μF ≤ 2u_{2^μ} + F` when `2K 2^μ ≤ F`. -/
theorem u_low {K F : PTm n} (μ : PTm n) (hK : Γ ⊢[PRAAx] le one K) (h2K : Γ ⊢[PRAAx] le (two * (K * pw two μ)) F) :
    Γ ⊢[PRAAx] le (μ * F) (two * U (pw two μ) K F + F) := by
  have p := S_pow2_lower F μ hK
  have hKT : Γ ⊢[PRAAx] le K (K * pw two μ) := by
    have q := le_scale K (one_le_pw' (le_succ_self (Γ := Γ) one) μ)
    ipra_le sl q
  have e := natEq (eq_add_of_le (S_mono F hKT))
  ipra_le sl p + sl h2K with 2 * e

/-! ## The arithmetic of the decrement -/

/-- `W = 72DT² + 48DA + 192D²T(σ+1) + 192D² + 24D²(19222T + 11070)`. -/
abbrev DecW (D A T s : PTm n) : PTm n :=
  num 72 * D * (T * T) + num 48 * (D * A) + num 192 * (D * D) * (T * succ s) + num 192 * (D * D) +
    num 24 * (D * D) * (num 19222 * T + num 11070)

/-- The integer condition of the step: `Z(2W + 3A²B) + 400ADBT ≤ 3ZA²Bμ`. -/
abbrev DecC (D A B T s μ Z : PTm n) : Fm PTm n :=
  le (Z * (two * DecW D A T s + num 3 * (A * A) * B) + num 400 * (A * D) * (B * T)) (Z * (num 3 * (A * A) * B) * μ)

theorem decrement_alg {r w ux uN u0 T s μ F x D A B Z N q : PTm n}
    (hraw : Γ ⊢[PRAAx] le (num 24 * (D * D) * w + num 3 * (A * A) * (F * F) * x * (B * u0) +
        num 96 * (D * D) * (F * x) * (uN * uN))
      (num 24 * D * (A * (F * (x * (uN * uN + two * (F * F))))) + num 96 * (D * D) * (F * x) * (ux * ux + two * (F * F)) +
        num 100 * (A * D) * (F * F) * (B * uN) * (N + q) +
        num 24 * (D * D) * (num 19222 * (F * F * (x * ux)) + num 11070 * (F * F * F * x))))
    (hw : Γ ⊢[PRAAx] le (ux * ux * r) w) (hN : Γ ⊢[PRAAx] le uN ux) (hxT : Γ ⊢[PRAAx] le ux (T * F))
    (hs : Γ ⊢[PRAAx] le ux (uN + succ s * F)) (h0 : Γ ⊢[PRAAx] le (μ * F) (two * u0 + F))
    (hZ : Γ ⊢[PRAAx] le (Z * (N + q)) (two * x)) (hC : Γ ⊢[PRAAx] DecC D A B T s μ Z)
    (hc1 : Γ ⊢[PRAAx] le one (num 48 * D * Z * (ux * ux))) :
    Γ ⊢[PRAAx] le (D * r + num 3 * (F * x)) (A * (F * x)) := by
  refine cancel_pos hc1 ?_
  ipra_le 2 * 𝔞 Z * sl hraw + 48 * 𝔞 D * 𝔞 D * 𝔞 Z * sl hw +
    48 * 𝔞 Z * 𝔞 D * 𝔞 A * 𝔞 F * 𝔞 x * 𝔞 ux * sl hN + 48 * 𝔞 Z * 𝔞 D * 𝔞 A * 𝔞 F * 𝔞 x * 𝔞 uN * sl hN +
    144 * 𝔞 Z * 𝔞 D * 𝔞 F * 𝔞 x * 𝔞 ux * sl hxT + 144 * 𝔞 Z * 𝔞 D * 𝔞 F * 𝔞 x * 𝔞 T * 𝔞 F * sl hxT +
    384 * 𝔞 Z * 𝔞 D * 𝔞 D * 𝔞 F * 𝔞 x * (𝔞 s + 1) * 𝔞 F * sl hxT +
    192 * 𝔞 Z * 𝔞 D * 𝔞 D * 𝔞 F * 𝔞 x * (𝔞 s + 1) * 𝔞 F * sl hN +
    192 * 𝔞 Z * 𝔞 D * 𝔞 D * 𝔞 F * 𝔞 x * 𝔞 ux * sl hs + 192 * 𝔞 Z * 𝔞 D * 𝔞 D * 𝔞 F * 𝔞 x * 𝔞 uN * sl hs +
    200 * 𝔞 A * 𝔞 D * 𝔞 F * 𝔞 F * 𝔞 B * 𝔞 uN * sl hZ +
    400 * 𝔞 A * 𝔞 D * 𝔞 F * 𝔞 F * 𝔞 B * 𝔞 x * sl hxT + 400 * 𝔞 A * 𝔞 D * 𝔞 F * 𝔞 F * 𝔞 B * 𝔞 x * sl hN +
    3 * 𝔞 A * 𝔞 A * 𝔞 F * 𝔞 F * 𝔞 x * 𝔞 B * 𝔞 Z * sl h0 + 𝔞 F * 𝔞 F * 𝔞 F * 𝔞 x * sl hC +
    922656 * 𝔞 D * 𝔞 D * 𝔞 F * 𝔞 F * 𝔞 x * 𝔞 Z * sl hxT

/-- `u² absd(a, b) ≤ absd(a u u, b u u)`. -/
theorem absd_sq {a b u : PTm n} : Γ ⊢[PRAAx] le (u * u * absd a b) (absd (a * u * u) (b * u * u)) := by
  have ea : Γ ⊢[PRAAx] u * u * a ≐ a * u * u := by ipra_ring
  have eb : Γ ⊢[PRAAx] u * u * b ≐ b * u * u := by ipra_ring
  exact le_congr (.eqRefl _) (congrAdd (congrMonus ea eb) (congrMonus eb ea)) (scale_absd (u * u) a b)

/-! ## The block hypothesis from the stage bound -/

/-- Every divisor `d ≤ N` with `NY ≤ x` has `Y ≤ ⌊x/d⌋ ≤ x`, so the stage bound holds on the block `(E₀, N]`. -/
theorem onblock_of_stage {x Y Ds A K L E0 N : PTm n} (hNY : Γ ⊢[PRAAx] le (N * Y) x)
    (hst : Γ ⊢[PRAAx] Stage x Y Ds A K L) : Γ ⊢[PRAAx] OnBlock x E0 N (stg x A Ds K L) := by
  have hNY' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift N * Syn.shift Y) (Syn.shift x) := by
    simpa [Fm.shift, Syn.shift] using hNY.shift
  have a := Prf.allE (quo (Syn.shift x) (var 0)) hst.shift
  simp only [Stage, Fm.shift, Fm.subst_all, Fm.subst_imp, Fm.subst_eq, subst_le, subst_lt, subst_ap2,
    PTm.subst_mul, PTm.subst_add, PTm.subst_monus, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
    Syn.subst_var, Syn.up_zero, Syn.inst_zero, subst_up_shift_pal, Syn.subst_inst_shift] at a
  have a' : (Γ.map Fm.shift) ⊢[PRAAx] lt (quo (Syn.shift x) (var 0)) (succ (Syn.shift x)) ⟶
      (le (Syn.shift Y) (quo (Syn.shift x) (var 0)) ⟶
        le (Syn.shift Ds * absd (Psi wt (quo (Syn.shift x) (var 0)) (pairT (Syn.shift K) (fact (Syn.shift L))))
            (fact (Syn.shift L) * quo (Syn.shift x) (var 0)))
          (Syn.shift A * (fact (Syn.shift L) * quo (Syn.shift x) (var 0)))) := by
    simpa [Syn.shift] using a
  refine .allI (.impI (.impI (.impI ?_)))
  let Θ : List (Fm PTm (n + 1)) := le (var 0) (Syn.shift N) :: lt (Syn.shift E0) (var 0) ::
    lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift
  have hv : Θ ⊢[PRAAx] le one (var 0) :=
    le_trans ((succ_monus_succ _ _).eqTrans (zero_le _)) (Prf.hyp1 : Θ ⊢[PRAAx] lt (Syn.shift E0) (var 0))
  have hq : Θ ⊢[PRAAx] le (quo (Syn.shift x) (var 0)) (Syn.shift x) := BlockInstance.quo_le_x _ hv
  have h1 : Θ ⊢[PRAAx] lt (quo (Syn.shift x) (var 0)) (succ (Syn.shift x)) := (succ_monus_succ _ _).eqTrans hq
  have h2 : Θ ⊢[PRAAx] le (Syn.shift Y) (quo (Syn.shift x) (var 0)) :=
    LeanProofs.IPRA.AnalyticNumberTheory.SumReindex.le_quo_of_mul_le (pos_of_one_le hv)
      (le_trans (mul_le_mul_right (Syn.shift Y) (Prf.hyp0 : Θ ⊢[PRAAx] le (var 0) (Syn.shift N))) hNY'.wk.wk.wk)
  exact Prf.impE (Prf.impE (a'.wk.wk.wk : Θ ⊢[PRAAx] _) h1) h2

/-! ## The decrement -/

/-- Lemma `con:one-step`, finitely: the stage bound on `[Y, x]` improves to `A − 3` at `x`. -/
theorem one_step_decrement {M x K L Ds A Y μ h B H0 T s Z : PTm n} (hx : Γ ⊢[PRAAx] le one x)
    (hK : Γ ⊢[PRAAx] le one K) (hx4 : Γ ⊢[PRAAx] le (Q4 x) K) (hL4 : Γ ⊢[PRAAx] le (K * Q4 x) L)
    (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L) (hKx : Γ ⊢[PRAAx] le (K * x) L)
    (hMx : Γ ⊢[PRAAx] le (succ M) x) (hY : Γ ⊢[PRAAx] le (succ M * Y) x) (hst : Γ ⊢[PRAAx] Stage x Y Ds A K L)
    (hBN : Γ ⊢[PRAAx] le (pw two μ * pw (pw two (h + h)) B) (succ M))
    (hxL : Γ ⊢[PRAAx] le x L) (hxK : Γ ⊢[PRAAx] le x K) (hNN : Γ ⊢[PRAAx] le (K * pw x x) L)
    (hA1 : Γ ⊢[PRAAx] le one A) (hA4 : Γ ⊢[PRAAx] le A (two * (two * Ds)))
    (hH0 : Γ ⊢[PRAAx] le (num 3 * (A * A) + num 384 * (Ds * Ds)) (num 16 * (Ds * (A * H0))))
    (hh : Γ ⊢[PRAAx] le (two * H0 + one) h) (hF : Γ ⊢[PRAAx] le (two * x) (fact L))
    (hxT : Γ ⊢[PRAAx] le x (pw two T)) (hxs : Γ ⊢[PRAAx] le x (succ M * pw two (succ s)))
    (hZN : Γ ⊢[PRAAx] le (Z * succ M) x) (hZ0 : Γ ⊢[PRAAx] le Z (pw two μ))
    (h2K : Γ ⊢[PRAAx] le (two * (K * pw two μ)) (fact L)) (hC : Γ ⊢[PRAAx] DecC Ds A B T s μ Z)
    (hZ1 : Γ ⊢[PRAAx] le one Z) (hD1 : Γ ⊢[PRAAx] le one Ds) (hux : Γ ⊢[PRAAx] le one (U x K (fact L))) :
    Γ ⊢[PRAAx] le (Ds * absd (Psi wt x (pairT K (fact L))) (fact L * x) + num 3 * (fact L * x)) (A * (fact L * x)) := by
  have raw := one_step_raw (N := succ M) hx hK hx4 hL4 hP hKx hMx hY hst (one_le_pw' (le_succ_self (Γ := Γ) one) μ) hBN
    (le_refl _) hxL hxK hNN hA1 hA4 hH0 hh hF (onblock_of_stage hY hst)
  have hN1 : Γ ⊢[PRAAx] le one (succ M) := (succ_monus_succ _ _).eqTrans (zero_le _)
  have hs := le_trans (u_mono K (fact L) hxs) (u_shift (K := K) (fact L) (succ s) hN1)
  have hq : Γ ⊢[PRAAx] le (quo x (pw two μ) * Z) (quo x (pw two μ) * pw two μ) := le_scale _ hZ0
  have hq2 := quo_mul_le (x := x) (pos_of_one_le (one_le_pw' (Γ := Γ) (le_succ_self (Γ := Γ) one) μ))
  have hZ : Γ ⊢[PRAAx] le (Z * (succ M + quo x (pw two μ))) (two * x) := by
    ipra_le sl hZN + sl hq + sl hq2
  have hc1 : Γ ⊢[PRAAx] le one (num 48 * Ds * Z * (U x K (fact L) * U x K (fact L))) := by
    have a := one_le_mul (one_le_mul hD1 hZ1) (one_le_mul hux hux)
    ipra_le 48 * sl a + 47
  have ep : Γ ⊢[PRAAx] inst2 psiB x (pairT K (fact L)) ≐ Psi wt x (pairT K (fact L)) := by
    rw [inst2_psiB]; exact .eqRefl _
  have eq : Γ ⊢[PRAAx] inst2 qB x (pairT K (fact L)) ≐ fact L * x := by
    rw [inst2_qB]; exact congrMul (snd_pair _ _) (.eqRefl _)
  have d := decrement_alg raw absd_sq (u_mono K (fact L) hMx)
    (le_trans (u_mono K (fact L) hxT) (u_pow K (fact L) T)) hs (u_low μ hK h2K) hZ hC hc1
  exact le_congr (congrAdd (congrMul (.eqRefl _) (congrAdd (congrMonus ep eq) (congrMonus eq ep))) (.eqRefl _))
    (.eqRefl _) d

end LeanProofs.IPRA.AnalyticNumberTheory.OneStepDecrement
