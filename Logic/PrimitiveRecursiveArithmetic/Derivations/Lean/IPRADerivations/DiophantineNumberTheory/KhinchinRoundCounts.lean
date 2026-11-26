import IPRADerivations.DiophantineNumberTheory.KhinchinRoundBits
import IPRADerivations.Core.Header

/-!
# One (K2) round from the per-cell (K11) counts (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`: "For each gap of positive length, apply
the block construction … If `R_j = |[0,1] ∖ U_j|`, (K11) gives `R_{j+1} ≤ (1 − 1/b₀) R_j`."

Coarse cell `g < G` has uncovered bit `w(g, x) ≤ 1`; its new block's fine coverage is `v(k, ⟨g, x⟩)` for the `r`
fine cells `k < r`. The per-cell (K11) count — `KhinchinBlock.block_cover`, confined to the cell by
`KhinchinBlockLocal.block_out` and localized by `Foundations.SumLocal.sum_local` — is
`w r ≤ (c+1) Σ_{k<r} sg(v(k))`. Then, with the round bits of `KhinchinRoundBits` packed as bodies in `g`
(`wB`, `rsB`, `cvB`, all with parameter `⟨r, x⟩`):

* `round_from_counts`: `(c+1) Σ_g rs_g ≤ c r Σ_g w_g` — the round contraction `(c+1) R_{j+1} ≤ c R_j` (fine unit),
  by `KhinchinGridRound.round_grid` with `cell_sum`, `cell_res`, `cell_cov` at every cell.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRoundCounts

open_ipra
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinGridRound (round_grid)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRoundBits (fB cB cell_sum cell_res cell_cov)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `w(g, x)` over `0 = g`, `1 = ⟨r, x⟩`. -/
def wB (w : PTm 2) : PTm 2 := Syn.subst ![var 0, sndT (var 1)] w

/-- The fine residual of cell `g`: `Σ_{k<r} f(k)` with `f(k) = w(g)[v(k, ⟨g, x⟩) = 0]`. -/
def rsB (w v : PTm 2) : PTm 2 := ap2 (sumF (fB v)) (fstT (var 1)) (pairT (wB w) (pairT (var 0) (sndT (var 1))))

/-- The newly covered fine cells of cell `g`: `Σ_{k<r} (1 − f(k))`. -/
def cvB (w v : PTm 2) : PTm 2 := ap2 (sumF (cB v)) (fstT (var 1)) (pairT (wB w) (pairT (var 0) (sndT (var 1))))

theorem inst2_wB (w : PTm 2) (g y : PTm n) : inst2 (wB w) g y = inst2 w g (sndT y) := by
  simp only [inst2, wB, Syn.subst_subst]; congr 1; funext j; fin_cases j <;> simp

theorem inst2_rsB (w v : PTm 2) (g y : PTm n) :
    inst2 (rsB w v) g y = ap2 (sumF (fB v)) (fstT y) (pairT (inst2 w g (sndT y)) (pairT g (sndT y))) := by
  rw [← inst2_wB]; simp [inst2, rsB]

theorem inst2_cvB (w v : PTm 2) (g y : PTm n) :
    inst2 (cvB w v) g y = ap2 (sumF (cB v)) (fstT y) (pairT (inst2 w g (sndT y)) (pairT g (sndT y))) := by
  rw [← inst2_wB]; simp [inst2, cvB]

/-- One round of (K2) from the per-cell (K11) counts: `(c+1) Σ_g rs_g ≤ c r Σ_g w_g`. -/
theorem round_from_counts (w v : PTm 2) (c r G x : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift G) ⟶
      le (inst2 w (var 0) (Syn.shift x)) one ⋏
        le (inst2 w (var 0) (Syn.shift x) * Syn.shift r)
          (succ (Syn.shift c) * ap2 (sumF (sg v)) (Syn.shift r) (pairT (var 0) (Syn.shift x))))) :
    Γ ⊢[PRAAx] le (succ c * ap2 (sumF (rsB w v)) G (pairT r x)) ((c * r) * ap2 (sumF (wB w)) G (pairT r x)) := by
  refine round_grid (wB w) (rsB w v) (cvB w v) c r G (pairT r x) (.allI (.impI ?_))
  let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift G) :: Γ.map Fm.shift
  have p := Prf.impE (h.allOpen.wk (ψ := lt (var 0) (Syn.shift G))) Prf.hyp0
  have p1 : Θ ⊢[PRAAx] le (inst2 w (var 0) (Syn.shift x)) one := Prf.andE₁ p
  have p2 := Prf.andE₂ p
  rw [show Syn.shift (pairT r x) = pairT (Syn.shift r) (Syn.shift x) by simp [Syn.shift], inst2_wB, inst2_rsB,
    inst2_cvB]
  have es := snd_pair (Γ := Θ) (Syn.shift r) (Syn.shift x)
  have ef := fst_pair (Γ := Θ) (Syn.shift r) (Syn.shift x)
  have eW : Θ ⊢[PRAAx] inst2 w (var 0) (sndT (pairT (Syn.shift r) (Syn.shift x))) ≐ inst2 w (var 0) (Syn.shift x) :=
    congrInst2 w (.eqRefl _) es
  have eP : Θ ⊢[PRAAx] pairT (inst2 w (var 0) (sndT (pairT (Syn.shift r) (Syn.shift x))))
        (pairT (var 0) (sndT (pairT (Syn.shift r) (Syn.shift x)))) ≐
      pairT (inst2 w (var 0) (Syn.shift x)) (pairT (var 0) (Syn.shift x)) :=
    congrPairT eW (congrPairT (.eqRefl _) es)
  have eRS := congrAp2 (sumF (fB v)) ef eP
  have eCV := congrAp2 (sumF (cB v)) ef eP
  have s := cell_sum v (Syn.shift r) (pairT (var 0) (Syn.shift x)) p1
  have rr := cell_res (Γ := Θ) v (inst2 w (var 0) (Syn.shift x)) (Syn.shift r) (pairT (var 0) (Syn.shift x))
  have cc := cell_cov v p1 p2
  refine .andI (.andI (le_congr eW.eqSymm (.eqRefl _) p1) ((congrAdd eRS eCV).eqTrans s)) (.andI ?_ ?_)
  · exact le_congr eRS.eqSymm (congrMul (.eqRefl _) eW.eqSymm) rr
  · exact le_congr (congrMul eW.eqSymm (.eqRefl _)) (congrMul (.eqRefl _) eCV.eqSymm) cc

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRoundCounts
