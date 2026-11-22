import IPRADerivations.AnalyticNumberTheory.DirichletLeibniz

/-!
# The Leibniz step of Selberg's symmetry formula (`pnt_ipra_constructive_2026-11-14`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `selberg.tex`, proof of Lemma
`sb:symmetry`: "Let `L(n) = log n` and define `(𝒟a)(n) = a(n) log n`. Since `log n = log d + log(n/d)`,
`𝒟(a * b) = (𝒟a) * b + a * (𝒟b)`. The divisor identity used earlier is `L = 𝟏 * Λ`. Applying `𝒟`
gives the exact pointwise identity `L² = L * Λ + 𝟏 * (𝒟Λ)` … Similarly `𝒟τ = 2L * 𝟏`."

For every weight `w` on primes, with the completely additive `L_w` and the weighted von Mangoldt
function `Λ_w` of `WeightedMangoldt` (for `w = log` these are `log` and `Λ`), and `m ≥ 1`:

* `lam_conv_one`: `(Λ_w * 𝟏)(m) = L_w(m)` (`thm:lambda-divsum` in convolution form);
* `selberg_leibniz`: `L_w(m)² = ((𝒟_w Λ_w) * 𝟏)(m) + (Λ_w * (𝒟_w 𝟏))(m)`, i.e.
  `L_w(m)² = Σ_{d ∣ m} L_w(d) Λ_w(d) + Σ_{d ∣ m} Λ_w(d) L_w(m/d)` — the packet's `L² = 𝟏 * (𝒟Λ) + Λ * L`;
* `tau_leibniz`: `L_w(m) τ(m) = ((𝒟_w 𝟏) * 𝟏)(m) + (𝟏 * (𝒟_w 𝟏))(m)`, i.e. `𝒟τ = L * 𝟏 + 𝟏 * L`
  (the packet's `2L * 𝟏` after the divisor involution `DivisorSwap.div_swap`).

Both are instances of `DirichletLeibniz.dirichlet_leibniz`. The rearrangement `Λ * L = 𝟏 * (Λ * Λ)`
(associativity of the finite convolution) and the Möbius-inverted form `μ * L² = Λ * Λ + 𝒟Λ` are not
derived here.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.SelbergLeibniz

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.WeightedMangoldt
open LeanProofs.IPRA.AnalyticNumberTheory.DirichletLeibniz (cvB conv DwB inst2_cvB inst2_DwB cv_at dirichlet_leibniz)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrEqb')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Selberg

variable (w : PTm 2)

/-- `Λ_w(d)` as a body over `0 = d`, `1 = y`. -/
abbrev lamF : PTm 2 := ap2 (sumF (lamB w)) (succ (var 0)) (pairT (var 0) (var 1))

theorem inst2_lamF (d y : PTm n) : inst2 (lamF w) d y = Lam w d y := by
  simp [inst2, subst_ap2]

/-- `(Λ_w * 𝟏)(m) = L_w(m)` for `m ≥ 1`. -/
theorem lam_conv_one {m y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] conv (lamF w) one m y ≐ Lw w m y := by
  refine .eqTrans ?_ (lambda_divsum w hm)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [show Syn.shift (pairT m y) = pairT (Syn.shift m) (Syn.shift y) by simp [Syn.shift]]
  refine (cv_at _ _ _ _ _).eqTrans ?_
  rw [inst2_lamF, inst2_DB, show inst2 (one : PTm 2) (quo (Syn.shift m) (var 0)) (Syn.shift y) = one by
    simp [inst2]]
  have f₁ : (lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift) ⊢[PRAAx]
      fstT (pairT (Syn.shift m) (Syn.shift y)) ≐ Syn.shift m := fst_pair _ _
  have s₁ : (lt (var 0) (Syn.shift (succ m)) :: Γ.map Fm.shift) ⊢[PRAAx]
      sndT (pairT (Syn.shift m) (Syn.shift y)) ≐ Syn.shift y := snd_pair _ _
  refine (congrMul (.eqRefl _) ((mul_comm _ _).eqTrans (one_mul _))).eqTrans ?_
  exact congrMul (congrMul (.eqRefl _) (congrEqb' (congrAp2 remF f₁.eqSymm (.eqRefl _)) (.eqRefl _)))
    (congrAp2 (sumF (lamB w)) (.eqRefl _) (congrPairT (.eqRefl _) s₁.eqSymm))

/-- The exact Leibniz form of Selberg's identity: `L_w² = 𝟏 * (𝒟_w Λ_w) + Λ_w * L_w`, at `m ≥ 1`. -/
theorem selberg_leibniz {m y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] Lw w m y * Lw w m y ≐ conv (DwB w (lamF w)) one m y + conv (lamF w) (DwB w one) m y :=
  (congrMul (.eqRefl _) (lam_conv_one w hm).eqSymm).eqTrans (dirichlet_leibniz w (lamF w) one hm)

/-- `𝒟_w τ = (𝒟_w 𝟏) * 𝟏 + 𝟏 * (𝒟_w 𝟏)`, at `m ≥ 1`, with `τ = 𝟏 * 𝟏`. -/
theorem tau_leibniz {m y : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] Lw w m y * conv one one m y ≐ conv (DwB w one) one m y + conv one (DwB w one) m y :=
  dirichlet_leibniz w one one hm

end Selberg

end LeanProofs.IPRA.AnalyticNumberTheory.SelbergLeibniz
