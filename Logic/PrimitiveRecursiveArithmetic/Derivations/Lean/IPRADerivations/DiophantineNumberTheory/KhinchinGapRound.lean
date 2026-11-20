import IPRADerivations.DiophantineNumberTheory.KhinchinBlock
import IPRADerivations.DiophantineNumberTheory.KhinchinRounds

/-!
# One round of the (K2) amplification over the gap list (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, §"Amplification by the finitely many
residual gaps": "For each gap of positive length, apply the block construction to its interior `J` and add its
block union to `U_j` … Freeze the old gap list at the beginning of the round: process each old gap once,
aggregate the new intervals … If `R_j = |[0,1] ∖ U_j|`, (K11) gives `R_{j+1} ≤ (1 − 1/b₀) R_j`."

The frozen gap list is indexed by `g < G`, with gap lengths `ℓ_g` and covered lengths `c_g` (bodies `ℓ`, `cv`
in the gap index, all on one common grid). (K11) supplies `ℓ_g ≤ b c_g` with `b = c + 1` for every gap; the
residual of gap `g` after the round is `ℓ_g ∸ c_g`.

* `res_pt`: `ℓ ≤ (c+1) v` gives `(c+1)(ℓ ∸ v) ≤ c ℓ`;
* `round_aggregate`: summed over the gap list, `(c+1) Σ_g (ℓ_g ∸ c_g) ≤ c Σ_g ℓ_g`;
* `round_contract`: if the new residual is at most `Σ_g (ℓ_g ∸ c_g)` and the gaps' total length is at most the old
  residual, then `(c+1) R_{j+1} ≤ c R_j` — exactly the per-round hypothesis of `KhinchinRounds.amplify`.

The construction of the gap list itself (endpoint sort, complement) is not derived here.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinGapRound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlock (sum_le_lin1)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `ℓ ≤ (c+1) v` gives `(c+1)(ℓ ∸ v) ≤ c ℓ`. -/
theorem res_pt {l v c : PTm n} (h : Γ ⊢[PRAAx] le l (succ c * v)) :
    Γ ⊢[PRAAx] le (succ c * monus l v) (c * l) := by
  refine .orE (le_total v l) ?_ ?_
  · have h' : (le v l :: Γ) ⊢[PRAAx] le l (succ c * v) := h.wk
    have e := natEq (eq_add_of_le (Prf.hyp0 : (le v l :: Γ) ⊢[PRAAx] le v l))
    ipra_le sl h' with (𝔞 c + 1) * e
  · have e := natEq (Prf.hyp0 : (le l v :: Γ) ⊢[PRAAx] le l v)
    ipra_le 𝔞 c * 𝔞 l with (𝔞 c + 1) * e

/-- The residual body `ℓ_g ∸ c_g`. -/
def resB (l cv : PTm 2) : PTm 2 := monus l cv

theorem inst2_resB (l cv : PTm 2) (g x : PTm n) :
    inst2 (resB l cv) g x = monus (inst2 l g x) (inst2 cv g x) := by simp [inst2, resB]

/-- Summed over the frozen gap list: `(c+1) Σ_g (ℓ_g ∸ c_g) ≤ c Σ_g ℓ_g`. -/
theorem round_aggregate (l cv : PTm 2) (c G x : PTm n)
    (hcov : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift G) ⟶
      le (inst2 l (var 0) (Syn.shift x)) (succ (Syn.shift c) * inst2 cv (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (succ c * ap2 (sumF (resB l cv)) G x) (c * ap2 (sumF l) G x) := by
  refine sum_le_lin1 _ _ _ _ _ _ _ (.allI (.impI ?_))
  have p := Prf.impE (hcov.allOpen.wk (ψ := lt (var 0) (Syn.shift G))) Prf.hyp0
  rw [inst2_resB, show Syn.shift (succ c) = succ (Syn.shift c) by simp [Syn.shift]]
  exact res_pt p

/-- One round: a new residual `R' ≤ Σ_g (ℓ_g ∸ c_g)` and an old residual `R ≥ Σ_g ℓ_g` satisfy
`(c+1) R' ≤ c R`, the hypothesis of `KhinchinRounds.amplify`. -/
theorem round_contract (l cv : PTm 2) {c G x R R' : PTm n}
    (hcov : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift G) ⟶
      le (inst2 l (var 0) (Syn.shift x)) (succ (Syn.shift c) * inst2 cv (var 0) (Syn.shift x))))
    (hnew : Γ ⊢[PRAAx] le R' (ap2 (sumF (resB l cv)) G x)) (hold : Γ ⊢[PRAAx] le (ap2 (sumF l) G x) R) :
    Γ ⊢[PRAAx] le (succ c * R') (c * R) := by
  have a := round_aggregate l cv c G x hcov
  ipra_le (𝔞 c + 1) * sl hnew + sl a + 𝔞 c * sl hold

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinGapRound
