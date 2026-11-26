import IPRADerivations.AnalyticNumberTheory.ZetaFiniteContract
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.Core.Header

/-!
# The error budget of the zeta finite contract (`zeta_functional_equation_ipra`)

Packet: `analytic-number-theory/zeta_functional_equation_ipra`, `finite_contract.md`, "Explicit finite
approximation to J": with

  `T = p + λ(B!) + 4`, `N = p + (B + 1) λ(T) + 4`, `D = 2(B + 2) T^B`, `q = p + λ(TD) + 4`,
  `r = p + λ(T) + 4`,

the four `norm1` errors `2 B! 2^{−2T}`, `4 T^{B+1} 2^{−3(N+1)²}`, `T D 2^{−q}`, `T 2^{−r}` — "Their sum is strictly
less than `2^{−p}`". Each is at most `2^{−p−3}` (cleared: `term · 2^{p+3} ≤ 2^{exponent}`), so the sum is at
most `2^{−p−1} < 2^{−p}`:

* `err_tail` (`t > T`), `err_series` (`n > N`), `err_mesh` (left rectangles), `err_point` (point evaluation);
* `pow_absorb`: `x ≤ 2^L` and `L + c ≤ E` give `x 2^c ≤ 2^E` — the only estimate used, with
  `x ≤ 2^{λ(x)}` (`ZetaFiniteContract.clog_spec`) and `T^{B+1} ≤ 2^{λ(T)(B+1)}`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.ZetaErrorBudget

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockGeo (congrPw2)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockScales (pw_mono2)
open LeanProofs.IPRA.AnalyticNumberTheory.ZetaFiniteContract (clog clog_spec)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `a ≤ b` gives `2^a ≤ 2^b`. -/
theorem pw2_mono {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (pw two a) (pw two b) := by
  have hz : ∀ t : PTm n, Γ ⊢[PRAAx] zero + t ≐ t := fun t => by apply deriveNat; ipra_simps; try ring
  exact le_congr (congrPw2 (hz a)) (congrPw2 (hz b)) (pw_mono2 (K0 := zero) h)

/-- `x ≤ 2^L` and `L + c ≤ E` give `x 2^c ≤ 2^E`. -/
theorem pow_absorb {x L c E : PTm n} (hx : Γ ⊢[PRAAx] le x (pw two L)) (hE : Γ ⊢[PRAAx] le (L + c) E) :
    Γ ⊢[PRAAx] le (x * pw two c) (pw two E) := by
  have eadd := natEq (pw_add (Γ := Γ) two L c)
  have mono := pw2_mono hE
  ipra_le sl mono + 𝔞 (pw two c) * sl hx with eadd

/-- The parameters of the contract. -/
abbrev Tp (p B : PTm n) : PTm n := p + clog (fact B) + num 4
abbrev Np (p B : PTm n) : PTm n := p + succ B * clog (Tp p B) + num 4
abbrev Dp (p B : PTm n) : PTm n := num 2 * (B + num 2) * pw (Tp p B) B
abbrev qp (p B : PTm n) : PTm n := p + clog (Tp p B * Dp p B) + num 4
abbrev rp (p B : PTm n) : PTm n := p + clog (Tp p B) + num 4

/-- `t > T`: `2 B! 2^{−2T} ≤ 2^{−p−3}`. -/
theorem err_tail (p B : PTm n) :
    Γ ⊢[PRAAx] le (num 2 * fact B * pw two (p + num 3)) (pw two (num 2 * Tp p B)) := by
  have hx := Prf.andE₁ (clog_spec (Γ := Γ) (fact B))
  have hE : Γ ⊢[PRAAx] le (clog (fact B) + (p + num 4)) (num 2 * Tp p B) := by
    ipra_le 𝔞 p + 𝔞 (clog (fact B)) + 4
  have a := pow_absorb hx hE
  have e := natEq ((congrPw2 (show Γ ⊢[PRAAx] p + num 4 ≐ succ (p + num 3) by ipra_ring)).eqTrans
    (pw_succ (Γ := Γ) two (p + num 3)))
  ipra_le sl a with 𝔞 (fact B) * e

/-- `n > N`: `4 T^{B+1} 2^{−3(N+1)²} ≤ 2^{−p−3}`. -/
theorem err_series (p B : PTm n) :
    Γ ⊢[PRAAx] le (num 4 * pw (Tp p B) (succ B) * pw two (p + num 3))
      (pw two (num 3 * (succ (Np p B) * succ (Np p B)))) := by
  have hT := Prf.andE₁ (clog_spec (Γ := Γ) (Tp p B))
  have hTB : Γ ⊢[PRAAx] le (pw (Tp p B) (succ B)) (pw two (clog (Tp p B) * succ B)) :=
    le_congr (.eqRefl _) (AnalyticNumberTheory.RSA.pw_mul two (clog (Tp p B)) (succ B)) (pw_le_pw (succ B) hT)
  have hE : Γ ⊢[PRAAx] le (clog (Tp p B) * succ B + (p + num 5)) (num 3 * (succ (Np p B) * succ (Np p B))) := by
    ipra_le 2 * (𝔞 p + 𝔞 B * 𝔞 (clog (Tp p B)) + 𝔞 (clog (Tp p B)) + 5) *
        (𝔞 p + 𝔞 B * 𝔞 (clog (Tp p B)) + 𝔞 (clog (Tp p B)) + 5) +
      (𝔞 p + 𝔞 B * 𝔞 (clog (Tp p B)) + 𝔞 (clog (Tp p B)) + 5) *
        (𝔞 p + 𝔞 B * 𝔞 (clog (Tp p B)) + 𝔞 (clog (Tp p B)) + 4)
  have a := pow_absorb hTB hE
  have e := natEq ((congrPw2 (show Γ ⊢[PRAAx] p + num 5 ≐ succ (succ (p + num 3)) by
    ipra_ring)).eqTrans
      ((pw_succ (Γ := Γ) two (succ (p + num 3))).eqTrans (congrMul (pw_succ (Γ := Γ) two (p + num 3)) (.eqRefl _))))
  ipra_le sl a with 𝔞 (pw (Tp p B) (succ B)) * e

/-- The left-rectangle mesh: `T D 2^{−q} ≤ 2^{−p−3}`. -/
theorem err_mesh (p B : PTm n) :
    Γ ⊢[PRAAx] le (Tp p B * Dp p B * pw two (p + num 3)) (pw two (qp p B)) := by
  have hx := Prf.andE₁ (clog_spec (Γ := Γ) (Tp p B * Dp p B))
  exact pow_absorb hx (by ipra_le 1)

/-- Point evaluation: `T 2^{−r} ≤ 2^{−p−3}`. -/
theorem err_point (p B : PTm n) : Γ ⊢[PRAAx] le (Tp p B * pw two (p + num 3)) (pw two (rp p B)) := by
  have hx := Prf.andE₁ (clog_spec (Γ := Γ) (Tp p B))
  exact pow_absorb hx (by ipra_le 1)

end LeanProofs.IPRA.AnalyticNumberTheory.ZetaErrorBudget
