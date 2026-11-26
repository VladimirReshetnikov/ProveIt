import IPRADerivations.Analysis.Stirling.Expansions.GaussianStirlingOddGrid

/-!
# Telescoping the odd-logarithm comparison

The left rectangle sum bounds the unreduced odd series from above.
The right rectangle sum bounds it from below up to a relative error
(1/G), at a finite cutoff of at least (G T) for a grid of length (T).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingOddGridTelescope

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.RobinLogName (Nz Nz_zero Nz_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma (Pv)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (cancel_pos)
open GaussianStirlingOddGrid (parameter numerator denominator denominator_positive grid_step)
open GammaMeshRobinLogBridge (leftSum rightSum left_zero right_zero left_succ right_succ)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem zero_power (k : PTm n) : Γ ⊢[PRAAx] Pv k zero ≐ zero := by
  apply deriveNat
  change Groth.ι (Q.mk Γ (pw zero (succ (two*k)))) = _
  ipra_simps
  simpa using natEq (pw_succ (Γ := Γ) zero (two*k))

private theorem zero_argument (K s : PTm n) : Γ ⊢[PRAAx] Nz K zero s ≐ zero := by
  have all : Γ ⊢[PRAAx] .all (Nz (var 0) zero (Syn.shift s) ≐ zero) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [Fm.subst_eq,subst_ap2,subst_pairT,ConciseIPRA.PTm.subst_zero,Syn.subst_var,
        Syn.inst_zero,Syn.subst_inst_shift] using Nz_zero (Γ := Γ) zero s
    · simp only [Fm.subst_eq,subst_ap2,subst_pairT,ConciseIPRA.PTm.subst_zero,Syn.subst_var,
        Syn.repl_zero,subst_repl_shift]
      let Δ := (Nz (var 0) zero (Syn.shift s) ≐ zero) :: Γ.map Fm.shift
      have e := natEq (Nz_succ (Γ := Δ) (var 0) zero (Syn.shift s))
      have h := natEq (Prf.hyp0 : Δ ⊢[PRAAx] _)
      have z := natEq (zero_power (Γ := Δ) (var 0))
      apply deriveNat
      ipra_simps
      rw [e,h,z]
      ring
  simpa only [Fm.subst_eq,subst_ap2,subst_pairT,ConciseIPRA.PTm.subst_zero,Syn.subst_var,
    Syn.inst_zero,Syn.subst_inst_shift] using all.allE K

def prefixBounds (X G K L i : PTm n) : Fm PTm n :=
  le (fact L*numerator X K i) (leftSum X i (fact L)*denominator X K i) ⋏
    le (G*rightSum X i (fact L)*denominator X K i)
      (fact L*G*numerator X K i+leftSum X i (fact L)*denominator X K i)

ipra_subst prefixBounds

private theorem prefix_zero (X G K L : PTm n) : Γ ⊢[PRAAx] prefixBounds X G K L zero := by
  have a := natEq (zero_argument (Γ := Γ) K (parameter X zero))
  have b := natEq (left_zero (Γ := Γ) X (fact L))
  have c := natEq (right_zero (Γ := Γ) X (fact L))
  refine .andI ?_ ?_
  · dsimp [numerator]
    ipra_le 0 using linear_combination 𝔞 (denominator X K zero)*b-𝔞 (fact L)*a
  · dsimp [numerator]
    ipra_le 0 using linear_combination 𝔞 (fact L)*𝔞 G*a+𝔞 (denominator X K zero)*b-𝔞 G*𝔞 (denominator X K zero)*c

private theorem prefix_step (X G K L T i : PTm n) (hX : Γ ⊢[PRAAx] le one X)
    (hK : Γ ⊢[PRAAx] le one K) (hG : Γ ⊢[PRAAx] le (G*T) K)
    (hT : Γ ⊢[PRAAx] le (X+T) L) (hi : Γ ⊢[PRAAx] le (succ i) T)
    (ih : Γ ⊢[PRAAx] prefixBounds X G K L i) : Γ ⊢[PRAAx] prefixBounds X G K L (succ i) := by
  have hcorner := le_trans (le_succ_self i) hi
  have pow : Γ ⊢[PRAAx] le (G*i) K := by ipra_le 𝔞 G*sl hcorner+sl hG
  have step := grid_step X G K L i hX hK pow (le_trans (add_le_add₂ (le_refl X) hi) hT)
  have a := natEq (left_succ X i (fact L) hX)
  have b := natEq (right_succ (Γ := Γ) X i (fact L))
  refine .andI ?_ ?_
  · apply cancel_pos (denominator_positive X K i hX)
    ipra_le 𝔞 (denominator X K (succ i))*sl ih.andE₁+sl step.andE₁ using
      linear_combination 𝔞 (denominator X K i)*𝔞 (denominator X K (succ i))*a
  · apply cancel_pos (denominator_positive X K i hX)
    ipra_le 𝔞 (denominator X K (succ i))*sl ih.andE₂+sl step.andE₂ using
      linear_combination 𝔞 (denominator X K i)*𝔞 (denominator X K (succ i))*a
        -𝔞 G*𝔞 (denominator X K i)*𝔞 (denominator X K (succ i))*b

theorem grid_telescope (X G K L T : PTm n) (hX : Γ ⊢[PRAAx] le one X)
    (hK : Γ ⊢[PRAAx] le one K) (hG : Γ ⊢[PRAAx] le (G*T) K) (hT : Γ ⊢[PRAAx] le (X+T) L) :
    Γ ⊢[PRAAx] prefixBounds X G K L T := by
  let sh (q : PTm n) := Syn.shift q
  have x : Γ.map Fm.shift ⊢[PRAAx] le one (sh X) := by simpa [Fm.shift,Syn.shift,sh] using hX.shift
  have k : Γ.map Fm.shift ⊢[PRAAx] le one (sh K) := by simpa [Fm.shift,Syn.shift,sh] using hK.shift
  have g : Γ.map Fm.shift ⊢[PRAAx] le (sh G*sh T) (sh K) := by simpa [Fm.shift,Syn.shift,sh] using hG.shift
  have h : Γ.map Fm.shift ⊢[PRAAx] le (sh X+sh T) (sh L) := by simpa [Fm.shift,Syn.shift,sh] using hT.shift
  have all : Γ ⊢[PRAAx] .all (le (var 0) (sh T) ⟶ prefixBounds (sh X) (sh G) (sh K) (sh L) (var 0)) := by
    ipra_qfind (by unfold prefixBounds; exact ⟨le_QF _ _,⟨le_QF _ _,le_QF _ _⟩⟩) [subst_le, subst_prefixBounds, sh]
    · exact .impI (prefix_zero X G K L)
    · exact .impI (prefix_step _ _ _ _ _ _ x.wk.wk k.wk.wk g.wk.wk h.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))
  have hFinal : Γ ⊢[PRAAx] le T T ⟶ prefixBounds X G K L T := by
    simpa only [Fm.subst_imp,subst_le,subst_prefixBounds,Syn.subst_var,sh,Syn.inst_zero,Syn.subst_inst_shift] using all.allE T
  exact .impE hFinal (le_refl _)

end LeanProofs.IPRA.Analysis.GaussianStirlingOddGridTelescope
