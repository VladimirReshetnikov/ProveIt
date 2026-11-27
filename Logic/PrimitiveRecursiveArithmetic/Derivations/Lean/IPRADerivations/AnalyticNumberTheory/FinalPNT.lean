import IPRADerivations.AnalyticNumberTheory.PiModulus

/-!
# The arithmetic prime number theorem in iPRA (`pnt_ipra_constructive_2026-11-14`, Theorem `thm:main`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `pnt_ipra.tex`, Theorem `thm:main` (Arithmetic
prime number theorem): "The following sentence is provable in first-order iPRA:
`∀k ∀n (k ≥ 1 ∧ n ≥ N(k)) → k dist(π(n)A(n), nF(n)) ≤ nF(n)`", with `F(n) = (n²)!`,
`A(n) = Σ_{j=n+1}^{n²} F(n)/j` (so `A(n)/F(n) = H_{n²} − H_n`), `dist(a, b) = (a ∸ b) + (b ∸ a)`, and `π(n)` the
number of primes `≤ n` (here `PiTheta.Pi n 0 = Σ_{d ≤ n} [d prime]`, primality by the least-prime-factor search
`Valuation.isP`, i.e. trial division).

`arith_pnt`: for `k ≥ 1` and `n ≥ N(k) = 2^{s_J + 131137 q³}` (`q = 5k`, `s_J` the stage exponent of
`StageInduction`, an explicit primitive-recursive function of `k`)

  `k · absd(π(n) A(n), n F(n)) ≤ n F(n)`.

It combines `PiModulus.pi_modulus` (`q|π(n)u_n − Fn| ≤ 4Fn` at the mesh `K = (n + 1)⁴` over `F = L!`) with the
change of mesh `K → n` (`MeshChange.mesh_change`, error `π(n)⌊F/n⌋ ≤ 2F`) and of denominator `L! → (n²)!`
(`MeshChange.S_denom`, exact); `final_alg` is the closing slack certificate.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.FinalPNT

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB quo_anti)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.StepParams (ell clog_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.StageAdvance (clog_ge)
open LeanProofs.IPRA.AnalyticNumberTheory.StageInduction (Jst sT)
open LeanProofs.IPRA.AnalyticNumberTheory.PsiModulus (Kx Lx)
open LeanProofs.IPRA.AnalyticNumberTheory.PiTheta (Pi piB inst2_piB pi_le)
open LeanProofs.IPRA.AnalyticNumberTheory.MeshChange (S_denom mesh_change)
open LeanProofs.IPRA.AnalyticNumberTheory.PiModulus (pi_modulus)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockInstance (quo_le_x)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTThresholds (Dq Q3)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le cancel_pos)
open LeanProofs.IPRA.Analysis.Products (fact)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The packet's terms -/

/-- `F(n) = (n²)!`. -/
abbrev Fn (m : PTm n) : PTm n := fact (m * m)
/-- `A(n) = Σ_{j=n+1}^{n²} F(n)/j = S(n², F(n)) − S(n, F(n))`. -/
abbrev An (m : PTm n) : PTm n := monus (S (m * m) (Fn m)) (S m (Fn m))
/-- `q = 5k`, written `q = p + 1`. -/
abbrev pk (k : PTm n) : PTm n := pred (num 5 * k)
/-- The modulus `N(k) = 2^{s_J + 131137 q³}`. -/
abbrev Nk (k : PTm n) : PTm n := pw two (sT (Jst (pk k)) (Dq (pk k)) + num 131137 * Q3 (pk k))

/-! ## The closing algebra -/

theorem final_alg {q F x pi u v c F0 A : PTm n}
    (h1 : Γ ⊢[PRAAx] le (q * (F * x)) (q * (u * pi) + num 3 * (F * x)))
    (h2 : Γ ⊢[PRAAx] le (q * (u * pi)) (q * (F * x) + num 4 * (F * x)))
    (hm1 : Γ ⊢[PRAAx] le v (u + c)) (hm2 : Γ ⊢[PRAAx] le u (v + c)) (hπ : Γ ⊢[PRAAx] le pi (succ x))
    (hcx : Γ ⊢[PRAAx] le (c * x) F) (hc : Γ ⊢[PRAAx] le c F) (hx2q : Γ ⊢[PRAAx] le (two * q) x)
    (hden : Γ ⊢[PRAAx] F0 * v ≐ F * A) (hF1 : Γ ⊢[PRAAx] le one F) :
    Γ ⊢[PRAAx] le (q * absd (pi * A) (x * F0)) (num 5 * (x * F0)) := by
  have e := natEq hden
  refine le_trans (scale_absd q _ _) (absd_le ?_ ?_)
  · refine cancel_pos hF1 ?_
    ipra_le 𝔞 F0 * sl h2 + 𝔞 q * 𝔞 F0 * 𝔞 pi * sl hm1 + 𝔞 q * 𝔞 F0 * 𝔞 c * sl hπ + 𝔞 q * 𝔞 F0 * sl hcx +
      𝔞 q * 𝔞 F0 * sl hc + 𝔞 F0 * 𝔞 F * sl hx2q with 𝔞 q * 𝔞 pi * e
  · refine cancel_pos hF1 ?_
    ipra_le 𝔞 F0 * sl h1 + 𝔞 q * 𝔞 F0 * 𝔞 pi * sl hm2 + 𝔞 q * 𝔞 F0 * 𝔞 c * sl hπ + 𝔞 q * 𝔞 F0 * sl hcx +
      𝔞 q * 𝔞 F0 * sl hc + 𝔞 F0 * 𝔞 F * sl hx2q + 𝔞 F * 𝔞 F0 * 𝔞 x with 𝔞 q * 𝔞 pi * e

/-! ## The conversions -/

/-- `π(n)` does not read the parameter of its body. -/
theorem pi_param (m z : PTm n) : Γ ⊢[PRAAx] Pi m z ≐ Pi m zero := by
  refine le_antisymm ?_ ?_
  · refine sum_le_params _ _ _ _ _ (.allI (.impI ?_)); rw [inst2_piB, inst2_piB]; exact le_refl _
  · refine sum_le_params _ _ _ _ _ (.allI (.impI ?_)); rw [inst2_piB, inst2_piB]; exact le_refl _

/-- The logarithms of `m` at the meshes `m` and `K`, over `F = L!`, differ by at most `⌊F/m⌋`. -/
theorem mesh_u {m K L : PTm n} (hm : Γ ⊢[PRAAx] le one m) (hmK : Γ ⊢[PRAAx] le m K)
    (hL : Γ ⊢[PRAAx] le (K * (m * m)) L) :
    Γ ⊢[PRAAx] le (U m m (fact L)) (U m K (fact L) + quo (fact L) m) ⋏
      le (U m K (fact L)) (U m m (fact L) + quo (fact L) m) := by
  have mc := mesh_change hm (le_trans hm hmK) hL
  have hqk := quo_anti (F := fact L) (pos_of_one_le hm) hmK
  have hmm : Γ ⊢[PRAAx] le m (m * m) := by have q := le_scale m hm; ipra_le sl q
  have hKK : Γ ⊢[PRAAx] le K (K * m) := by have q := le_scale K hm; ipra_le sl q
  have e1 := natEq (eq_add_of_le (S_mono (fact L) hmm))
  have e2 := natEq (eq_add_of_le (S_mono (fact L) hKK))
  refine .andI ?_ ?_
  · ipra_le sl (Prf.andE₁ mc) + sl hqk with e1 - e2
  · ipra_le sl (Prf.andE₂ mc) with e2 - e1

/-- `F(n) u^{(n)}_n = F A(n)`: the change of denominator `L! → (n²)!`. -/
theorem den_change {m L : PTm n} (hm : Γ ⊢[PRAAx] le one m) (hL : Γ ⊢[PRAAx] le (m * m) L) :
    Γ ⊢[PRAAx] Fn m * U m m (fact L) ≐ fact L * An m := by
  have hmm : Γ ⊢[PRAAx] le m (m * m) := by have q := le_scale m hm; ipra_le sl q
  ipra_lc natEq (S_denom (le_refl (m * m)) hL) - natEq (S_denom hmm hL) -
    𝔞 (fact (m * m)) * natEq (eq_add_of_le (S_mono (fact L) hmm)) +
    𝔞 (fact L) * natEq (eq_add_of_le (S_mono (Fn m) hmm))

/-! ## The theorem -/

/-- Theorem `thm:main`: `k · dist(π(n) A(n), n F(n)) ≤ n F(n)` for `k ≥ 1`, `n ≥ N(k)`. -/
theorem arith_pnt {k m : PTm n} (hk : Γ ⊢[PRAAx] le one k) (hm : Γ ⊢[PRAAx] le (Nk k) m) :
    Γ ⊢[PRAAx] le (k * absd (Pi m zero * An m) (m * Fn m)) (m * Fn m) := by
  have p2 : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := pos_of_one_le (le_succ_self one)
  have h5 : Γ ⊢[PRAAx] le one (num 5 * k) := by ipra_le 5 * sl hk + 4
  have eq5 := pos_of_one_le h5
  have e5 := natEq eq5
  -- the size of `n`
  have hE1 : Γ ⊢[PRAAx] le one (sT (Jst (pk k)) (Dq (pk k)) + num 131137 * Q3 (pk k)) := by
    ipra_le 𝔞 (sT (Jst (pk k)) (Dq (pk k))) + 131137 * 𝔞 (pk k) ^ 3 + 393411 * 𝔞 (pk k) ^ 2 + 393411 * 𝔞 (pk k) + 131136
  have hJ : Γ ⊢[PRAAx] le (pw two (sT (Jst (pk k)) (Dq (pk k)))) m :=
    le_trans (pw_le_exp p2 (le_add_right _ _)) hm
  have h2m : Γ ⊢[PRAAx] le two m := le_trans (le_congr (pw_one two) (.eqRefl _) (pw_le_exp p2 hE1)) hm
  have hm1 : Γ ⊢[PRAAx] le one m := le_trans (le_succ_self one) h2m
  have hcl := clog_ge hm
  have ec := natEq (pos_of_one_le (clog_pos h2m))
  have hl : Γ ⊢[PRAAx] le (num 131136 * Q3 (pk k)) (ell m) := by
    ipra_le sl hcl + 𝔞 (sT (Jst (pk k)) (Dq (pk k))) + 𝔞 (pk k) ^ 3 + 3 * 𝔞 (pk k) ^ 2 + 3 * 𝔞 (pk k) with ec
  have hx2q : Γ ⊢[PRAAx] le (two * succ (pk k)) m := by
    have a := le_pow_self (Γ := Γ) (sT (Jst (pk k)) (Dq (pk k)) + num 131137 * Q3 (pk k))
    ipra_le sl a + sl hm + 𝔞 (sT (Jst (pk k)) (Dq (pk k))) + 131137 * 𝔞 (pk k) ^ 3 + 393411 * 𝔞 (pk k) ^ 2 + 393409 * 𝔞 (pk k) + 131135
  -- the estimate at the mesh `K = (n + 1)⁴`
  have pm := pi_modulus (p := pk k) hJ hl
  have pz := pi_param (Γ := Γ) m (pairT (Kx m) (fact (Lx m)))
  have h1 := le_congr (.eqRefl _) (congrAdd (congrMul (.eqRefl _) (congrMul (.eqRefl _) pz)) (.eqRefl _)) (Prf.andE₁ pm)
  have h2 := le_congr (congrMul (.eqRefl _) (congrMul (.eqRefl _) pz)) (.eqRefl _) (Prf.andE₂ pm)
  -- the change of mesh and of denominator
  have hmK : Γ ⊢[PRAAx] le m (Kx m) := by ipra_le 𝔞 m ^ 4 + 4 * 𝔞 m ^ 3 + 6 * 𝔞 m ^ 2 + 3 * 𝔞 m + 1
  have hLm : Γ ⊢[PRAAx] le (Kx m * (m * m)) (Lx m) := by
    ipra_le (𝔞 m + 1) ^ 4 * (4 * 𝔞 m ^ 3 + 5 * 𝔞 m ^ 2 + 4 * 𝔞 m + 1 + 𝔞 m ^ 4 + 𝔞 (pw two (two * (two * m))) + 𝔞 (pw m m))
  have hmL : Γ ⊢[PRAAx] le (m * m) (Lx m) := le_trans (by
    have q := le_scale (m * m) (show Γ ⊢[PRAAx] le one (Kx m) by ipra_le 𝔞 m ^ 4 + 4 * 𝔞 m ^ 3 + 6 * 𝔞 m ^ 2 + 4 * 𝔞 m)
    ipra_le sl q) hLm
  have hmu := mesh_u hm1 hmK hLm
  have hden := den_change hm1 hmL
  have hF1 : Γ ⊢[PRAAx] le one (fact (Lx m)) :=
    le_congr (.eqRefl _) (LeanProofs.IPRA.AnalyticNumberTheory.Primes.fact_pos _).eqSymm ((succ_monus_succ _ _).eqTrans (zero_le _))
  have fa := final_alg h1 h2 (Prf.andE₁ hmu) (Prf.andE₂ hmu) (pi_le m zero)
    (quo_mul_le (x := fact (Lx m)) (pos_of_one_le hm1)) (quo_le_x _ hm1) hx2q hden hF1
  refine cancel_pos (c := num 5) (by ipra_le 4) ?_
  ipra_le sl fa with (𝔞 (monus (Pi m zero * An m) (m * Fn m)) + 𝔞 (monus (m * Fn m) (Pi m zero * An m))) * e5

end LeanProofs.IPRA.AnalyticNumberTheory.FinalPNT
