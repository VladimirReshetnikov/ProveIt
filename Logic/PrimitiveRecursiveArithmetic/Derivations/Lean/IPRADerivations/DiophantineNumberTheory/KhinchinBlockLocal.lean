import IPRADerivations.DiophantineNumberTheory.KhinchinBlockScales
import IPRADerivations.DiophantineNumberTheory.KhinchinMargin

/-!
# A scale of the (K11) block covers only cells of its gap (`hurwitz_khinchin_ipra`)

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`: "All added intervals are inside the gap in
which they were constructed." This instantiates `Foundations.CoverLocal.cover_out` and `KhinchinMargin.member_in`
on the actual scale family of `KhinchinScale`/`KhinchinBlockScales`: at a scale with parameters
`tup M Q' T α γ β` and width `w`, the member `j` is `[A_j, A_j + sg(act_j) w)` with `A_j = ⌊T p/q⌋`,
`p = j mod M`, `q = Q' + ⌊j/M⌋ + 1`, `act_j = [qα < pβ][pβ < qγ][gcd(p, q) = 1]` (`KhinchinScale.A_at`, `act_at`).

* `member_local`: every member is inactive (empty) or, by `KhinchinSeparated.act_facts` and
  `KhinchinMargin.scale_margin`, inside the gap `[L, H)` with margins `Lβ ≤ Tα`, `Tγ + wβ ≤ Hβ`;
* `scale_out`: the scale's cover bit vanishes at every cell outside `[L, H)`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockLocal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (sg_bit)
open LeanProofs.IPRA.Foundations.IntervalCover (covB)
open LeanProofs.IPRA.Foundations.IntervalPacking (loB hiB inst2_loB inst2_hiB)
open LeanProofs.IPRA.Foundations.CoverLocal (cover_out congrSg')
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinScale (tup AK actK AE actE qE A_at act_at)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinSeparated (act_facts)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinMargin (scale_margin member_in)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A member of the scale family is empty or inside the gap `[L, H)`. -/
theorem member_local {j x w M Q' T α γ β L H : PTm n} (hx : Γ ⊢[PRAAx] x ≐ pairT w (tup M Q' T α γ β))
    (hβ : Γ ⊢[PRAAx] β ≐ succ (pred β)) (hL : Γ ⊢[PRAAx] le (L * β) (T * α))
    (hH : Γ ⊢[PRAAx] le (T * γ + w * β) (H * β)) :
    Γ ⊢[PRAAx] le (inst2 (hiB AK actK) j x) (inst2 (loB AK) j x) ⋎
      (le L (inst2 (loB AK) j x) ⋏ le (inst2 (hiB AK actK) j x) H) := by
  have ey : Γ ⊢[PRAAx] sndT x ≐ tup M Q' T α γ β := (congrSnd hx).eqTrans (snd_pair _ _)
  have ew : Γ ⊢[PRAAx] fstT x ≐ w := (congrFst hx).eqTrans (fst_pair _ _)
  have eA : Γ ⊢[PRAAx] inst2 AK j (sndT x) ≐ AE Q' T M j :=
    (congrInst2 AK (.eqRefl _) ey).eqTrans (A_at j M Q' T α γ β)
  have eAct : Γ ⊢[PRAAx] inst2 actK j (sndT x) ≐ actE Q' M α γ β j :=
    (congrInst2 actK (.eqRefl _) ey).eqTrans (act_at j M Q' T α γ β)
  have eLo : Γ ⊢[PRAAx] inst2 (loB AK) j x ≐ AE Q' T M j := by
    rw [inst2_loB]; exact eA
  have eHi : Γ ⊢[PRAAx] inst2 (hiB AK actK) j x ≐ AE Q' T M j + sg (actE Q' M α γ β j) * w := by
    rw [inst2_hiB]; exact congrAdd eA (congrMul (congrSg' eAct) ew)
  have hq : Γ ⊢[PRAAx] qE Q' M j ≐ succ (pred (qE Q' M j)) := congrSucc (pred_succ _).eqSymm
  have hcase : Γ ⊢[PRAAx] (sg (actE Q' M α γ β j) ≐ zero) ⋎
      (le L (AE Q' T M j) ⋏ le (AE Q' T M j + w) H) := by
    refine .orE (sg_bit (actE Q' M α γ β j)) (.orI₁ Prf.hyp0) (.orI₂ ?_)
    have f := act_facts (Prf.hyp0 : ((sg (actE Q' M α γ β j) ≐ one) :: Γ) ⊢[PRAAx] sg (actE Q' M α γ β j) ≐ one)
    exact scale_margin hq.wk hβ.wk (Prf.andE₁ f) (Prf.andE₁ (Prf.andE₂ f)) hL.wk hH.wk
  have m := member_in hcase
  refine .orE m ?_ ?_
  · exact .orI₁ (le_congr eHi.wk.eqSymm eLo.wk.eqSymm Prf.hyp0)
  · exact .orI₂ (.andI (le_congr (.eqRefl _) eLo.wk.eqSymm (Prf.andE₁ Prf.hyp0))
      (le_congr eHi.wk.eqSymm (.eqRefl _) (Prf.andE₂ Prf.hyp0)))

/-- A scale of the block covers no cell outside the gap `[L, H)`. -/
theorem scale_out {c K w M Q' T α γ β L H : PTm n}
    (hβ : Γ ⊢[PRAAx] β ≐ succ (pred β)) (hL : Γ ⊢[PRAAx] le (L * β) (T * α))
    (hH : Γ ⊢[PRAAx] le (T * γ + w * β) (H * β)) (hc : Γ ⊢[PRAAx] lt c L ⋎ le H c) :
    Γ ⊢[PRAAx] inst2 (covB (loB AK) (hiB AK actK)) c (pairT K (pairT w (tup M Q' T α γ β))) ≐ zero := by
  refine cover_out (loB AK) (hiB AK actK) (.allI (.impI ?_)) hc
  let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift K) :: Γ.map Fm.shift
  have sh : ∀ {φ : Fm PTm n}, (Γ ⊢[PRAAx] φ) → (Θ ⊢[PRAAx] Fm.shift φ) := fun h => h.shift.wk
  have hβ' : Θ ⊢[PRAAx] Syn.shift β ≐ succ (pred (Syn.shift β)) := by simpa [Fm.shift, Syn.shift] using sh hβ
  have hL' : Θ ⊢[PRAAx] le (Syn.shift L * Syn.shift β) (Syn.shift T * Syn.shift α) := by
    simpa [Fm.shift, Syn.shift] using sh hL
  have hH' : Θ ⊢[PRAAx] le (Syn.shift T * Syn.shift γ + Syn.shift w * Syn.shift β) (Syn.shift H * Syn.shift β) := by
    simpa [Fm.shift, Syn.shift] using sh hH
  have hx : Θ ⊢[PRAAx] Syn.shift (pairT w (tup M Q' T α γ β)) ≐
      pairT (Syn.shift w) (tup (Syn.shift M) (Syn.shift Q') (Syn.shift T) (Syn.shift α) (Syn.shift γ) (Syn.shift β)) := by
    rw [show Syn.shift (pairT w (tup M Q' T α γ β)) =
      pairT (Syn.shift w) (tup (Syn.shift M) (Syn.shift Q') (Syn.shift T) (Syn.shift α) (Syn.shift γ) (Syn.shift β)) by
        simp [Syn.shift, tup]]
    exact .eqRefl _
  exact member_local hx hβ' hL' hH'

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockLocal
