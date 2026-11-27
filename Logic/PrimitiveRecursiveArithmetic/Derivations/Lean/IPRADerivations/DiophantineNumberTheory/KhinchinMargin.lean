import IPRADerivations.AnalyticNumberTheory.SumReindex
import IPRADerivations.Foundations.CoverLocal

/-!
# The scale intervals stay inside their gap (`hurwitz_khinchin_ipra`, (K8))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`: "`J^* = (a + L/4, b − L/4)` … the
centers lie in `J^*` and `r_k ≤ 1/(8Q²) ≤ L/4`", so every interval of `E_k(J)` lies in `J`; and "All added
intervals are inside the gap in which they were constructed."

On the grid `T`, the fraction `p/q ∈ J^* = (α/β, γ/β)` (`qα < pβ < qγ`) sits at `A = ⌊Tp/q⌋`, and its member is
`[A, A + [act] w)`. For a gap `[L, H)` of the grid with margins `Lβ ≤ Tα` and `Tγ + wβ ≤ Hβ`:

* `scale_margin`: `L ≤ A` and `A + w ≤ H`;
* `member_in`: a member `[A, A + sg(act) w)` that is inactive (`sg act = 0`) or has the margins is empty or inside
  `[L, H)` — the per-member hypothesis of `Foundations.CoverLocal.cover_out`, so the (K11) block built in a gap
  covers only cells of that gap.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinMargin

open_ipra exports
open LeanProofs.IPRA.Signum (sg)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `⌊x/q⌋ q ≤ x` for `q ≥ 1`. -/
theorem quo_mul_le {x q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) : Γ ⊢[PRAAx] le (quo x q * q) x :=
  Division.quo_mul_le hq

/-- Cancel a factor `b = succ (pred b)`. -/
theorem cancel {b u v : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (h : Γ ⊢[PRAAx] le (b * u) (b * v)) :
    Γ ⊢[PRAAx] le u v :=
  mul_le_cancel (le_congr (congrMul hb (.eqRefl _)) (congrMul hb (.eqRefl _)) h)

/-- `p/q ∈ (α/β, γ/β)` with the margins `Lβ ≤ Tα`, `Tγ + wβ ≤ Hβ` gives `L ≤ ⌊Tp/q⌋` and `⌊Tp/q⌋ + w ≤ H`. -/
theorem scale_margin {T p q α β γ L H w : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q))
    (hβ : Γ ⊢[PRAAx] β ≐ succ (pred β)) (h1 : Γ ⊢[PRAAx] lt (q * α) (p * β)) (h2 : Γ ⊢[PRAAx] lt (p * β) (q * γ))
    (hL : Γ ⊢[PRAAx] le (L * β) (T * α)) (hH : Γ ⊢[PRAAx] le (T * γ + w * β) (H * β)) :
    Γ ⊢[PRAAx] le L (quo (T * p) q) ⋏ le (quo (T * p) q + w) H := by
  have h1' := le_of_lt h1
  have h2' := le_of_lt h2
  refine .andI ?_ ?_
  · refine le_quo_of_mul_le hq (cancel hβ ?_)
    ipra_le 𝔞 q * sl hL + 𝔞 T * sl h1'
  · have m := quo_mul_le (Γ := Γ) (x := T * p) hq
    have hA : Γ ⊢[PRAAx] le (quo (T * p) q * β) (T * γ) := by
      refine cancel hq ?_
      ipra_le 𝔞 β * sl m + 𝔞 T * sl h2'
    refine cancel hβ ?_
    ipra_le sl hA + sl hH

/-- `h ∸ j ≤ h`. -/
alias monus_le' := Common.monus_le_self

/-- `sg a ≤ 1`. -/
alias sg_le_one := Common.sg_le_one

/-- A member `[A, A + sg(act) w)` that is inactive or inside the margins is empty or inside `[L, H)`. -/
theorem member_in {A act w L H : PTm n} (h : Γ ⊢[PRAAx] (sg act ≐ zero) ⋎ (le L A ⋏ le (A + w) H)) :
    Γ ⊢[PRAAx] le (A + sg act * w) A ⋎ (le L A ⋏ le (A + sg act * w) H) := by
  refine .orE h ?_ ?_
  · have e := natEq (Prf.hyp0 : ((sg act ≐ zero) :: Γ) ⊢[PRAAx] sg act ≐ zero)
    exact .orI₁ (by ipra_le 0 with -(𝔞 w * e))
  · have s := sg_le_one (Γ := (le L A ⋏ le (A + w) H) :: Γ) act
    have hH : ((le L A ⋏ le (A + w) H) :: Γ) ⊢[PRAAx] le (A + w) H := Prf.andE₂ Prf.hyp0
    exact .orI₂ (.andI (Prf.andE₁ Prf.hyp0) (by ipra_le sl hH + 𝔞 w * sl s))

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinMargin

export_ipra DiophantineNumberTheory.KhinchinMargin (cancel)
