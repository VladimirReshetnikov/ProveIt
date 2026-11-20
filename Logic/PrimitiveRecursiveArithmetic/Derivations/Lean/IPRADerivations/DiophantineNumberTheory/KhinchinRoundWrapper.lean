import IPRADerivations.DiophantineNumberTheory.KhinchinCellBridge
import IPRADerivations.DiophantineNumberTheory.KhinchinRoundCounts

/-!
# One (K2) round from the cells' block counts (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`: "For each gap of positive length, apply
the block construction to its interior … (K11) gives `R_{j+1} ≤ (1 − 1/b₀) R_j`", `b₀ = 16384`.

The round's data are packed in `x = ⟨r, ⟨B, ⟨K₀, ⟨M, ⟨R, ⟨G', p⟩⟩⟩⟩⟩⟩`: `G = p + 1` coarse cells, `r` fine cells each, the
grid `T = R! G' = rG`, and in cell `g` the block of `KhinchinBlock.block_cover` with the parameters of
`KhinchinCellParams`. The new fine coverage of cell `g` is the body `vB wb` (the block's union, at fine cell
`rg + k`).

* `vB_at`: `sg(v(k, ⟨g, x⟩)) = sg(⋃_g)(rg + k)` — the decoding of the packed parameters (`tmpl`, `Prf.eqCongr`);
* `k2_round`: if every cell's block satisfies the conclusion of `block_cover` and the margins of `block_out`, and
  the coarse bits are `w ≤ 1`, then `16384 R_{j+1} ≤ 16383 r R_j` (`R_{j+1} = Σ_g rs_g` fine, `R_j = Σ_g w_g`
  coarse) — `KhinchinCellBridge.cell_bridge` at every cell inside `KhinchinRoundCounts.round_from_counts`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRoundWrapper

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockScales (Xt bB)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinCellParams (αc γc b0c)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinCellBridge (cell_bridge)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRoundCounts (round_from_counts rsB wB)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The packed round parameters `⟨r, ⟨B, ⟨K₀, ⟨M, ⟨R, ⟨G', p⟩⟩⟩⟩⟩⟩`. -/
abbrev px (r B K0 M R G' p : PTm n) : PTm n :=
  pairT r (pairT B (pairT K0 (pairT M (pairT R (pairT G' p)))))

/-- The cell's union bit at fine cell `rg + k`, as a template in `0 = r, 1 = g, 2 = k, 3 = B, 4 = K₀, 5 = M, 6 = R,
7 = G', 8 = p`. -/
def tmpl (wb : PTm 2) : PTm 9 :=
  Syn.subst ![var 0 * var 1 + var 2,
    pairT (var 3) (Xt (var 4) (var 5) (var 6) (var 7) (αc (var 1)) (γc (var 1)) (b0c (var 8)))] (oB (bB wb))

/-- The new fine coverage `v(k, ⟨g, x⟩)`. -/
def vB (wb : PTm 2) : PTm 2 :=
  Syn.subst ![fstT (sndT (var 1)), fstT (var 1), var 0, fstT (sndT (sndT (var 1))),
    fstT (sndT (sndT (sndT (var 1)))), fstT (sndT (sndT (sndT (sndT (var 1))))),
    fstT (sndT (sndT (sndT (sndT (sndT (var 1)))))), fstT (sndT (sndT (sndT (sndT (sndT (sndT (var 1))))))),
    sndT (sndT (sndT (sndT (sndT (sndT (sndT (var 1)))))))] (tmpl wb)

theorem inst2_vB (wb : PTm 2) (k y : PTm n) :
    inst2 (vB wb) k y = Syn.subst ![fstT (sndT y), fstT y, k, fstT (sndT (sndT y)), fstT (sndT (sndT (sndT y))),
      fstT (sndT (sndT (sndT (sndT y)))), fstT (sndT (sndT (sndT (sndT (sndT y))))),
      fstT (sndT (sndT (sndT (sndT (sndT (sndT y)))))), sndT (sndT (sndT (sndT (sndT (sndT (sndT y))))))] (tmpl wb) := by
  simp only [inst2, vB]
  rw [Syn.subst_subst]
  exact congrArg (fun σ => Syn.subst σ (tmpl wb)) (funext fun i => by fin_cases i <;> simp)

theorem tmpl_at (wb : PTm 2) (r g k B K0 M R G' p : PTm n) :
    Syn.subst ![r, g, k, B, K0, M, R, G', p] (tmpl wb) =
      inst2 (oB (bB wb)) (r * g + k) (pairT B (Xt K0 M R G' (αc g) (γc g) (b0c p))) := by
  simp only [inst2, tmpl]
  rw [Syn.subst_subst]
  exact congrArg (fun σ => Syn.subst σ (oB (bB wb))) (funext fun i => by fin_cases i <;> simp [Xt])

/-- Decoding: `sg(v(k, ⟨g, x⟩))` is the cell's union bit at fine cell `rg + k`. -/
theorem vB_at (wb : PTm 2) (k g r B K0 M R G' p : PTm n) :
    Γ ⊢[PRAAx] inst2 (sg (vB wb)) k (pairT g (px r B K0 M R G' p)) ≐
      inst2 (offB (sg (oB (bB wb)))) k (pairT (r * g) (pairT B (Xt K0 M R G' (αc g) (γc g) (b0c p)))) := by
  have e0 : Γ ⊢[PRAAx] sndT (pairT g (px r B K0 M R G' p)) ≐ px r B K0 M R G' p := snd_pair _ _
  have e1 := (congrSnd e0).eqTrans (snd_pair (Γ := Γ) r _)
  have e2 := (congrSnd e1).eqTrans (snd_pair (Γ := Γ) B _)
  have e3 := (congrSnd e2).eqTrans (snd_pair (Γ := Γ) K0 _)
  have e4 := (congrSnd e3).eqTrans (snd_pair (Γ := Γ) M _)
  have e5 := (congrSnd e4).eqTrans (snd_pair (Γ := Γ) R _)
  have er : Γ ⊢[PRAAx] fstT (sndT (pairT g (px r B K0 M R G' p))) ≐ r := (congrFst e0).eqTrans (fst_pair _ _)
  have eg : Γ ⊢[PRAAx] fstT (pairT g (px r B K0 M R G' p)) ≐ g := fst_pair _ _
  have eB : Γ ⊢[PRAAx] fstT (sndT (sndT (pairT g (px r B K0 M R G' p)))) ≐ B := (congrFst e1).eqTrans (fst_pair _ _)
  have eK : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (pairT g (px r B K0 M R G' p))))) ≐ K0 :=
    (congrFst e2).eqTrans (fst_pair _ _)
  have eM : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (pairT g (px r B K0 M R G' p)))))) ≐ M :=
    (congrFst e3).eqTrans (fst_pair _ _)
  have eR : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (sndT (pairT g (px r B K0 M R G' p))))))) ≐ R :=
    (congrFst e4).eqTrans (fst_pair _ _)
  have eG : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (sndT (sndT (sndT (pairT g (px r B K0 M R G' p)))))))) ≐ G' :=
    (congrFst e5).eqTrans (fst_pair _ _)
  have ep : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (sndT (sndT (sndT (pairT g (px r B K0 M R G' p)))))))) ≐ p :=
    (congrSnd e5).eqTrans (snd_pair _ _)
  have eα := congrAdd (congrMul (.eqRefl (num 4)) eg) (.eqRefl (one : PTm n))
  have eγ := congrAdd (congrMul (.eqRefl (num 4)) eg) (.eqRefl (num 3 : PTm n))
  have eb := congrAdd (congrMul (.eqRefl (num 4)) ep) (.eqRefl (num 3 : PTm n))
  have eX := congrPairT eK (congrPairT eM (congrPairT eR (congrPairT eG (congrPairT eα (congrPairT eγ eb)))))
  have hv : Γ ⊢[PRAAx] inst2 (vB wb) k (pairT g (px r B K0 M R G' p)) ≐
      inst2 (oB (bB wb)) (r * g + k) (pairT B (Xt K0 M R G' (αc g) (γc g) (b0c p))) := by
    rw [inst2_vB wb k (pairT g (px r B K0 M R G' p)),
      tmpl_at wb (fstT (sndT (pairT g (px r B K0 M R G' p)))) (fstT (pairT g (px r B K0 M R G' p))) k
        (fstT (sndT (sndT (pairT g (px r B K0 M R G' p)))))
        (fstT (sndT (sndT (sndT (pairT g (px r B K0 M R G' p))))))
        (fstT (sndT (sndT (sndT (sndT (pairT g (px r B K0 M R G' p)))))))
        (fstT (sndT (sndT (sndT (sndT (sndT (pairT g (px r B K0 M R G' p))))))))
        (fstT (sndT (sndT (sndT (sndT (sndT (sndT (pairT g (px r B K0 M R G' p)))))))))
        (sndT (sndT (sndT (sndT (sndT (sndT (sndT (pairT g (px r B K0 M R G' p)))))))))]
    exact congrInst2 (oB (bB wb)) (congrAdd (congrMul er eg) (.eqRefl k)) (congrPairT eB eX)
  rw [show inst2 (sg (vB wb)) k (pairT g (px r B K0 M R G' p)) = sg (inst2 (vB wb) k (pairT g (px r B K0 M R G' p)))
      by simp [inst2, Signum.sg], inst2_offB,
    show ∀ (c y : PTm n), inst2 (sg (oB (bB wb))) c y = sg (inst2 (oB (bB wb)) c y) from fun c y => by
      simp [inst2, Signum.sg]]
  have ec : Γ ⊢[PRAAx] inst2 (oB (bB wb)) (fstT (pairT (r * g) (pairT B (Xt K0 M R G' (αc g) (γc g) (b0c p)))) + k)
      (sndT (pairT (r * g) (pairT B (Xt K0 M R G' (αc g) (γc g) (b0c p))))) ≐
        inst2 (oB (bB wb)) (r * g + k) (pairT B (Xt K0 M R G' (αc g) (γc g) (b0c p))) :=
    congrInst2 _ (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)
  exact LeanProofs.IPRA.Foundations.CoverLocal.congrSg' (hv.eqTrans ec.eqSymm)

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinRoundWrapper
