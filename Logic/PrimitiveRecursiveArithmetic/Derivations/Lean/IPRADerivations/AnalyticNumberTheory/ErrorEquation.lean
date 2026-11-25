import IPRADerivations.AnalyticNumberTheory.ChebyshevAbel

/-!
# The equation for the error term (`pnt_ipra_constructive_2026-11-14`, `sb:error-equation`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, Lemma `sb:error-equation`:
for `E_R(x) = R(x) log x + Σ_{n≤x} Λ(n) R(x/n)`, `R(y) = ψ(y) − y`, "`|E_R(x)| ≤ 4096x`". The proof: partial
summation (`ChebyshevAbel`), `Σ_{n≤x} (Λ * Λ)(n) = Σ_{n≤x} Λ(n) ψ(x/n)`, the symmetry bound (`SymmetryBound`), which
together give `|ψ(x) log x + Σ Λ(n) ψ(x/n) − 2x log x| ≤ 2052x`, and finally Mertens' estimate for
`x(Σ Λ(n)/n − log x)`.

Scaled by `F = L!` with the harmonic logarithm `u_x = F λ_K(x)`, and by `G = x!` to clear the fractions `x/n`
(`S_w(x) = Σ_{n≤x} Λ(n) G/n`, `HarmonicLambda.Sw`):

* `A_split`: `A_w(x) = Σ_{n≤x} Λ(n) L_w(n) + T₂(x)`, `T₂(x) = Σ_{d≤x} Λ(d) ψ(⌊x/d⌋)` (`ConvSummatory.conv_summatory`);
* `U_mono`, `ls_upper`, `ls_lower`: `x u_x − 2xF ≤ Σ_{n≤x} L_w(n) ≤ x u_x` (`HarmonicLogSum`, `lw_lower`);
* `cheb_upper`, `cheb_lower`: `|ψ(x) u_x + T₂(x) − 2F x u_x| ≤ 2208 F² x`;
* `error_upper`, `error_lower`: `|G (ψ(x) u_x + T₂(x)) − (G F x u_x + F x S_w(x))| ≤ 4096 G F² x`, the scaled
  `|E_R(x)| ≤ 4096x`: indeed `G F² E_R(x) = G(ψ(x) − Fx) u_x + G T₂(x) − F x S_w(x)`.

Hypotheses: `x ≥ 1`, `K ≥ 1`, `(x+1)⁴ ≤ K`, `K (x+1)⁴ ≤ L`, `K 2^{4x} ≤ L`, `K x^x ≤ L`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.ErrorEquation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono wt)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale mertens_upper)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertensLower (lw_lower mertens_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSum (PB inst2_PB log_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLambda (Sw)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi LamB pos_of_lt_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt (Lam Lw)
open LeanProofs.IPRA.AnalyticNumberTheory.SelbergLeibniz (lamF)
open LeanProofs.IPRA.AnalyticNumberTheory.WeightBridge (lw_le_u sum_le_add_const)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryInstances (bs_shift)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryPointwise (quo_mul_le le_Q4 le_succ')
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetryBound (gL Aw Ls symmetry_upper symmetry_lower)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetrySum (GxB inst2_GxB)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusSummatory (gS inst2_gS)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevAbel (auB adB abel_gen lam0 I_le lwB inst2_lwB lam_bridge)
open LeanProofs.IPRA.AnalyticNumberTheory.FourthRootSum (Q4)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (bS inst2_bS Bs RB conv_summatory)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (cvF inst2_cvF)
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (DwB)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHarmonic (shift_fact')
open LeanProofs.IPRA.Foundations.AuxiliaryEnvelope (sum_le_const)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## `A_w = Σ Λ L_w + Σ_d Λ(d) ψ(x/d)` -/

/-- `T₂(x) = Σ_{d≤x} Λ(d) ψ(⌊x/d⌋)`. -/
abbrev T2 (x K L : PTm n) : PTm n := ap2 (sumF (RB (lamF wt) (lamF wt))) (succ x) (pairT x (pairT K (fact L)))

theorem A_split (x K L : PTm n) :
    Γ ⊢[PRAAx] Aw x K L ≐ ap2 (sumF lwB) (succ x) (pairT K (fact L)) + T2 x K L := by
  have s := sum_add2 (Γ := Γ) lwB (cvF (lamF wt) (lamF wt)) (GxB wt) (K := succ x) (x := pairT K (fact L))
    (x' := pairT K (fact L)) (z := pairT K (fact L)) (.allI (.impI (by
      rw [inst2_GxB, inst2_lwB, inst2_cvF]
      ipra_ring)))
  exact s.eqTrans (congrAdd (.eqRefl _) (conv_summatory (lamF wt) (lamF wt) x _))

/-! ## `Σ_{n≤x} L_w(n)` against `x u_x` -/

theorem U_mono {k m K : PTm n} (F : PTm n) (hkm : Γ ⊢[PRAAx] le (succ k) m) :
    Γ ⊢[PRAAx] le (U (succ k) K F) (U m K F) := by
  have m1 : Γ ⊢[PRAAx] le (S K F) (S (K * succ k) F) :=
    S_mono F (le_of_eq_add (d := K * k) (by ipra_ring))
  have m2 : Γ ⊢[PRAAx] le (S (K * succ k) F) (S (K * m) F) := S_mono F (le_scale K hkm)
  have m3 : Γ ⊢[PRAAx] le (S K F) (S (K * m) F) := le_trans m1 m2
  have Eu := natEq (eq_add_of_le m1)
  have Eum := natEq (eq_add_of_le m3)
  ipra_le sl m2 with Eum - Eu

theorem inst2_gL (k y : PTm n) : inst2 gL k y = Lw wt k y * one := by simp [inst2, DwB]

theorem ls_zero (y : PTm n) : Γ ⊢[PRAAx] inst2 (gS gL) zero y ≐ zero := by
  rw [inst2_gS]; exact zero_mul_l sg_zero _

/-- `Σ_{n≤x} L_w(n) ≤ x u_x`. -/
theorem ls_upper {x K L : PTm n} (hK : Γ ⊢[PRAAx] le one K) (hKx : Γ ⊢[PRAAx] le (K * x) L) :
    Γ ⊢[PRAAx] le (Ls x K L) (x * U x K (fact L)) := by
  have hK' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK.shift
  have hKx' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * Syn.shift x) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hKx.shift
  have s := sum_le_const (Γ := Γ) (bS (gS gL)) (N := x) (L := U x K (fact L)) (x := pairT K (fact L))
    (.allI (.impI (by
      rw [inst2_bS, inst2_gS, inst2_gL, shift_pairT, shift_fact',
        show Syn.shift (U x K (fact L)) = U (Syn.shift x) (Syn.shift K) (fact (Syn.shift L)) by simp [Syn.shift]]
      let C := (lt (var 0) (Syn.shift x) :: Γ.map Fm.shift)
      have hv : C ⊢[PRAAx] le (succ (var 0)) (Syn.shift x) := Prf.hyp0
      have lu := lw_le_u hK'.wk (le_trans (le_scale _ hv) hKx'.wk)
      have um := U_mono (Γ := C) (K := Syn.shift K) (fact (Syn.shift L)) hv
      have e := natEq (sg_succ (Γ := C) (var 0))
      ipra_le sl lu + sl um with 𝔞 (Lw wt (succ (var 0)) (pairT (Syn.shift K) (fact (Syn.shift L)))) * e)))
  have b := natEq (bs_shift (Γ := Γ) (gS gL) x (pairT K (fact L)))
  have z := natEq (ls_zero (Γ := Γ) (pairT K (fact L)))
  ipra_le sl s with b + z

/-- `x u_x ≤ Σ_{n≤x} L_w(n) + 2xF`. -/
theorem ls_lower {x K L : PTm n} (hx : Γ ⊢[PRAAx] le one x) (hK : Γ ⊢[PRAAx] le one K)
    (hKx : Γ ⊢[PRAAx] le (K * x) L) (hxx : Γ ⊢[PRAAx] le (x * x) K) :
    Γ ⊢[PRAAx] le (x * U x K (fact L)) (Ls x K L + two * (x * fact L)) := by
  have hK' : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift K) := by simpa [Fm.shift, Syn.shift] using hK.shift
  have hKx' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift K * Syn.shift x) (Syn.shift L) := by
    simpa [Fm.shift, Syn.shift] using hKx.shift
  have ls := Prf.andE₁ (log_sum hK hKx)
  have sb := sum_le_add_const (Γ := Γ) PB (bS (gS gL)) (x := pairT K (fact L)) (y := pairT K (fact L))
    (c := S K (fact L) + x * quo (fact L) K) (N := x) (.allI (.impI (by
      rw [inst2_PB, inst2_bS, inst2_gS, inst2_gL, shift_pairT, shift_fact',
        show Syn.shift (S K (fact L) + x * quo (fact L) K) =
          S (Syn.shift K) (fact (Syn.shift L)) + Syn.shift x * quo (fact (Syn.shift L)) (Syn.shift K) by
          simp [Syn.shift]]
      let C := (lt (var 0) (Syn.shift x) :: Γ.map Fm.shift)
      have hv : C ⊢[PRAAx] le (succ (var 0)) (Syn.shift x) := Prf.hyp0
      have eS : C ⊢[PRAAx] S (fstT (pairT (Syn.shift K) (fact (Syn.shift L))) * succ (var 0))
          (sndT (pairT (Syn.shift K) (fact (Syn.shift L)))) ≐ S (Syn.shift K * succ (var 0)) (fact (Syn.shift L)) :=
        congrAp2 (sumF hB) (congrMul (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)
      refine le_congr eS.eqSymm (.eqRefl _) ?_
      have lw := lw_lower (le_succ' (zero_le (var 0))) hK'.wk (le_trans (le_scale _ hv) hKx'.wk)
      have mq := mul_le_mul_right (quo (fact (Syn.shift L)) (Syn.shift K)) hv
      have e := natEq (sg_succ (Γ := C) (var 0))
      ipra_le sl lw + sl mq with 𝔞 (Lw wt (succ (var 0)) (pairT (Syn.shift K) (fact (Syn.shift L)))) * e)))
  have b := natEq (bs_shift (Γ := Γ) (gS gL) x (pairT K (fact L)))
  have z := natEq (ls_zero (Γ := Γ) (pairT K (fact L)))
  have wx := natEq (pos_of_lt_zero hx)
  have hKK : Γ ⊢[PRAAx] le K (K * x) :=
    le_of_eq_add (d := K * pred x) (by apply deriveNat; ipra_simps; linear_combination 𝔞 K * wx)
  have eU := natEq (eq_add_of_le (S_mono (fact L) hKK))
  have q1 := mul_le_mul_right (quo (fact L) K) hxx
  have q2 := quo_mul_le (Γ := Γ) (x := fact L) (pos_of_lt_zero hK)
  have fx := le_scale (fact L) hx
  ipra_le sl ls + sl sb + sl q1 + sl q2 + sl fx with b + z + 𝔞 x * eU

/-! ## The symmetric Chebyshev estimate -/

section Alg
variable {psiU T Sau I Slw A Ls' xU F x : PTm n} (ab : Γ ⊢[PRAAx] Sau + I ≐ psiU) (sp : Γ ⊢[PRAAx] A ≐ Slw + T)
include ab sp

theorem cheb_alg_up (iI : Γ ⊢[PRAAx] le I (x * (two * (two * (F * F)))))
    (br : Γ ⊢[PRAAx] le Sau (Slw + two * (two * (F * F))))
    (su : Γ ⊢[PRAAx] le A (two * (F * Ls') + num 2200 * (F * F * x))) (lu : Γ ⊢[PRAAx] le Ls' xU)
    (hx : Γ ⊢[PRAAx] le one x) :
    Γ ⊢[PRAAx] le (psiU + T) (two * (F * xU) + num 2208 * (F * F * x)) := by
  have a := natEq ab; have b := natEq sp
  ipra_le sl iI + sl br + sl su + 2 * 𝔞 F * sl lu + 4 * (𝔞 F * 𝔞 F) * sl hx with a + b

theorem cheb_alg_lo (br : Γ ⊢[PRAAx] le Slw Sau)
    (sl' : Γ ⊢[PRAAx] le (two * (F * Ls')) (A + num 2200 * (F * F * x)))
    (ll : Γ ⊢[PRAAx] le xU (Ls' + two * (x * F))) :
    Γ ⊢[PRAAx] le (two * (F * xU)) (psiU + T + num 2204 * (F * F * x)) := by
  have a := natEq ab; have b := natEq sp
  ipra_le sl br + sl sl' + 2 * 𝔞 F * sl ll + 𝔞 I with a + b

end Alg

theorem hKx' {x K L : PTm n} (hL : Γ ⊢[PRAAx] le (K * Q4 x) L) : Γ ⊢[PRAAx] le (K * x) L :=
  le_trans (le_scale K (le_Q4 x)) hL

theorem hxx' {x K : PTm n} (hx4 : Γ ⊢[PRAAx] le (Q4 x) K) : Γ ⊢[PRAAx] le (x * x) K := by
  have h : Γ ⊢[PRAAx] le (x * x) (Q4 x) := by
    ipra_le 𝔞 x * 𝔞 x * 𝔞 x * 𝔞 x + 4 * (𝔞 x * 𝔞 x * 𝔞 x) + 5 * (𝔞 x * 𝔞 x) + 4 * 𝔞 x + 1
  exact le_trans h hx4

theorem eU' {x K L : PTm n} (hx : Γ ⊢[PRAAx] le one x) :
    Γ ⊢[PRAAx] S (K * x) (fact L) ≐ S K (fact L) + U x K (fact L) := by
  have wx := natEq (pos_of_lt_zero hx)
  have hKK : Γ ⊢[PRAAx] le K (K * x) :=
    le_of_eq_add (d := K * pred x) (by apply deriveNat; ipra_simps; linear_combination 𝔞 K * wx)
  exact eq_add_of_le (S_mono (fact L) hKK)

section Cheb
variable {x K L : PTm n} (hx : Γ ⊢[PRAAx] le one x) (hK : Γ ⊢[PRAAx] le one K) (hx4 : Γ ⊢[PRAAx] le (Q4 x) K)
  (hL : Γ ⊢[PRAAx] le (K * Q4 x) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
include hx hK hx4 hL hP

/-- `ψ(x) u_x + Σ_d Λ(d) ψ(x/d) ≤ 2F x u_x + 2208 F² x`. -/
theorem cheb_upper :
    Γ ⊢[PRAAx] le (Psi wt x (pairT K (fact L)) * U x K (fact L) + T2 x K L)
      (two * (fact L * (x * U x K (fact L))) + num 2208 * (fact L * fact L * x)) :=
  cheb_alg_up (abel_gen (LamB wt) x K (fact L) (lam0 K (fact L))) (A_split x K L) (I_le hK hP (le_refl x))
    (Prf.andE₂ (lam_bridge hK hx4 hP (hKx' hL))) (symmetry_upper hx hK hx4 hL) (ls_upper hK (hKx' hL)) hx

/-- `2F x u_x ≤ ψ(x) u_x + Σ_d Λ(d) ψ(x/d) + 2204 F² x`. -/
theorem cheb_lower :
    Γ ⊢[PRAAx] le (two * (fact L * (x * U x K (fact L))))
      (Psi wt x (pairT K (fact L)) * U x K (fact L) + T2 x K L + num 2204 * (fact L * fact L * x)) :=
  cheb_alg_lo (abel_gen (LamB wt) x K (fact L) (lam0 K (fact L))) (A_split x K L)
    (Prf.andE₁ (lam_bridge hK hx4 hP (hKx' hL))) (symmetry_lower hx hK hx4 hL)
    (ls_lower hx hK (hKx' hL) (hxx' hx4))

end Cheb

/-! ## The error equation -/

section ErrAlg
variable {G psiU T F x U Sw SKx SK q : PTm n} (eU : Γ ⊢[PRAAx] SKx ≐ SK + U) (hx : Γ ⊢[PRAAx] le one x)
include eU hx

theorem err_alg_up (cu : Γ ⊢[PRAAx] le (psiU + T) (two * (F * (x * U)) + num 2208 * (F * F * x)))
    (ml : Γ ⊢[PRAAx] le (G * SKx) (Sw + G * (SK + F + x * q))) (qq : Γ ⊢[PRAAx] le (x * (x * q)) F) :
    Γ ⊢[PRAAx] le (G * (psiU + T)) (G * (F * (x * U)) + F * (x * Sw) + num 4096 * (G * (F * F * x))) := by
  have e := natEq eU
  ipra_le 𝔞 G * sl cu + 𝔞 F * 𝔞 x * sl ml + 𝔞 G * 𝔞 F * sl qq + 𝔞 G * 𝔞 F * 𝔞 F * sl hx +
    1886 * (𝔞 G * 𝔞 F * 𝔞 F * 𝔞 x) with 𝔞 F * 𝔞 x * 𝔞 G * e

theorem err_alg_lo (cl : Γ ⊢[PRAAx] le (two * (F * (x * U))) (psiU + T + num 2204 * (F * F * x)))
    (mu : Γ ⊢[PRAAx] le (Sw + G * SK) (G * (SKx + q + two * (two * F)))) (xq : Γ ⊢[PRAAx] le (x * q) F) :
    Γ ⊢[PRAAx] le (G * (F * (x * U)) + F * (x * Sw)) (G * (psiU + T) + num 4096 * (G * (F * F * x))) := by
  have e := natEq eU
  ipra_le 𝔞 G * sl cl + 𝔞 F * 𝔞 x * sl mu + 𝔞 G * 𝔞 F * sl xq + 𝔞 G * 𝔞 F * 𝔞 F * sl hx +
    1887 * (𝔞 G * 𝔞 F * 𝔞 F * 𝔞 x) with 𝔞 F * 𝔞 x * 𝔞 G * e

end ErrAlg

section Err
variable {x K L : PTm n} (hx : Γ ⊢[PRAAx] le one x) (hK : Γ ⊢[PRAAx] le one K) (hx4 : Γ ⊢[PRAAx] le (Q4 x) K)
  (hL : Γ ⊢[PRAAx] le (K * Q4 x) L) (hP : Γ ⊢[PRAAx] le (K * pw two (two * (two * x))) L)
  (hX : Γ ⊢[PRAAx] le (K * pw x x) L)
include hx hK hx4 hL hP hX

omit hX in
/-- `sb:error-equation`, upper half, scaled: `G(ψ(x) u_x + T₂(x)) ≤ G F x u_x + F x S_w(x) + 4096 G F² x`. -/
theorem error_upper :
    Γ ⊢[PRAAx] le (fact x * (Psi wt x (pairT K (fact L)) * U x K (fact L) + T2 x K L))
      (fact x * (fact L * (x * U x K (fact L))) + fact L * (x * Sw wt x (pairT K (fact L))) +
        num 4096 * (fact x * (fact L * fact L * x))) := by
  have q1 := mul_le_mul_right (quo (fact L) K) (hxx' hx4)
  have q2 := quo_mul_le (Γ := Γ) (x := fact L) (pos_of_lt_zero hK)
  have qq : Γ ⊢[PRAAx] le (x * (x * quo (fact L) K)) (fact L) := by ipra_le sl q1 + sl q2
  exact err_alg_up (eU' hx (K := K) (L := L)) hx (cheb_upper hx hK hx4 hL hP)
    (mertens_lower hx hK (hKx' hL)) qq

/-- `sb:error-equation`, lower half, scaled: `G F x u_x + F x S_w(x) ≤ G(ψ(x) u_x + T₂(x)) + 4096 G F² x`. -/
theorem error_lower :
    Γ ⊢[PRAAx] le (fact x * (fact L * (x * U x K (fact L))) + fact L * (x * Sw wt x (pairT K (fact L))))
      (fact x * (Psi wt x (pairT K (fact L)) * U x K (fact L) + T2 x K L) +
        num 4096 * (fact x * (fact L * fact L * x))) := by
  have q1 := mul_le_mul_right (quo (fact L) K) (le_trans (le_Q4 x) hx4)
  have q2 := quo_mul_le (Γ := Γ) (x := fact L) (pos_of_lt_zero hK)
  have xq : Γ ⊢[PRAAx] le (x * quo (fact L) K) (fact L) := by ipra_le sl q1 + sl q2
  exact err_alg_lo (eU' hx (K := K) (L := L)) hx (cheb_lower hx hK hx4 hL hP)
    (mertens_upper hx hK hX hP) xq

end Err

end LeanProofs.IPRA.AnalyticNumberTheory.ErrorEquation
