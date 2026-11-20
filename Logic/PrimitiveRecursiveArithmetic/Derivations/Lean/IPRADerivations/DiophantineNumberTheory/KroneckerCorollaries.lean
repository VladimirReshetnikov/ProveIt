import IPRADerivations.DiophantineNumberTheory.ConicCount
import IPRADerivations.DiophantineNumberTheory.SimultaneousTransfer

/-!
# Arithmetic of the Kronecker corollaries

Packet: `diophantine-number-theory/dirichlet_kronecker_ipra`.

* `rational_compat` (`cor:rational`): "all generator residues are rational multiples of `1/D`. Their finite rational
  maximum is decidably either zero or at least `1/D` ... In the other case `D·D(h) ≥ 1 ≥ ρ(hβ)`": with
  `D(h) = e/D` (natural numerator `e`) and `ρ(hβ) = ρ'/Q ≤ 1/2`, either `e = 0` or `ρ' ≤ e Q`, i.e.
  `ρ(hβ) ≤ D·D(h)`, the strong compatibility with `C(H) = D`;
* `positive_window` (`eq:positiveq`): "If the returned coefficient is `q'` with `|q'| < N`, set `q = B + N + q'`.
  Then `B + 1 ≤ q ≤ B + 2N − 1`";
* `zero_passes` (`thm:alternative`): "The zero vector cannot fail: there `U_0 = e_0 < 1/8` and `L_0 = 0`": with
  `e_0 = e/Q`, `64(C+1)e ≤ Q` and `Q ≥ 1` give `8e < Q`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.KroneckerCorollaries

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.PolynomialRemainder (AbsLe abs_hi abs_lo)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `cor:rational`: the residue numerator is `0`, or `ρ(hβ) ≤ 1/2 ≤ D·D(h)`. -/
theorem rational_compat (e : PTm n) {ρ Q : PTm n} (hρ : Γ ⊢[PRAAx] le (num 2 * ρ) Q) :
    Γ ⊢[PRAAx] (e ≐ zero) ⋎ le ρ (e * Q) := by
  refine .orE (zero_or_succ e) (.orI₁ Prf.hyp0) (.orI₂ ?_)
  have he := natEq (Prf.hyp0 : ((e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] e ≐ succ (pred e))
  have h := hρ.wk (ψ := e ≐ succ (pred e))
  ipra_le sl h + 𝔟 ρ + 𝔟 (pred e) * 𝔟 Q using
    rw [he]; ring

/-- `eq:positiveq`: `|q'| ≤ b` with `b + 1 ≤ N` gives `B + 1 ≤ B + N + q' ≤ B + 2N − 1`. -/
theorem positive_window {q' : ZT n} {b N B : PTm n} (hq : Γ ⊢[PRAAx] AbsLe q' b) (hb : Γ ⊢[PRAAx] le (succ b) N) :
    Γ ⊢[PRAAx] zle (ZT.ofNat (succ B)) (ZT.ofNat (B + N) + q') ⋏
      zle (ZT.ofNat (B + N) + q' + ZT.ofNat one) (ZT.ofNat (B + N + N)) := by
  have hi := abs_hi hq
  have hl := abs_lo hq
  refine .andI ?_ ?_
  · show Γ ⊢[PRAAx] le (succ B + (zero + q'.neg)) ((B + N + q'.pos) + zero)
    ipra_le sl hl + sl hb
  · show Γ ⊢[PRAAx] le (B + N + q'.pos + one + zero) (B + N + N + (zero + q'.neg + zero))
    ipra_le sl hi + sl hb

/-- `thm:alternative`: the zero vector passes, `8e < Q`. -/
theorem zero_passes {C e Q : PTm n} (H1 : Γ ⊢[PRAAx] le (num 64 * succ C * e) Q) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] lt (num 8 * e) Q := by
  show Γ ⊢[PRAAx] le (succ (num 8 * e)) Q
  refine .orE (zero_or_succ e) ?_ ?_
  · have he := natEq (Prf.hyp0 : ((e ≐ zero) :: Γ) ⊢[PRAAx] e ≐ zero)
    have h := hQ.wk (ψ := e ≐ zero)
    ipra_le sl h using
      rw [he]; ring
  · have he := natEq (Prf.hyp0 : ((e ≐ succ (pred e)) :: Γ) ⊢[PRAAx] e ≐ succ (pred e))
    have h := H1.wk (ψ := e ≐ succ (pred e))
    ipra_le sl h + 64 * 𝔟 C * 𝔟 e + 56 * 𝔟 (pred e) + 55 using
      rw [he]; ring

end LeanProofs.IPRA.DiophantineNumberTheory.KroneckerCorollaries
