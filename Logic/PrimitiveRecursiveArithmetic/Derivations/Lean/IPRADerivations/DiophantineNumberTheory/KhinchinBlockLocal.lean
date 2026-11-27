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

open_ipra exports
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (sg_bit)
open LeanProofs.IPRA.Foundations.IntervalPacking (loB hiB inst2_loB inst2_hiB)
open LeanProofs.IPRA.Foundations.CoverLocal (cover_out congrSg')
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinScale (tup AK actK AE actE qE A_at act_at)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinSeparated (act_facts)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinMargin (scale_margin member_in)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockScales (Xt bB b_at Kk Qk)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Signum (sg_zero)

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


/-- The whole (K11) block covers no cell outside the gap `[L, H)`: the union bit `sg(Σ_{k<B} scale-k bit)` of
`KhinchinBlock.block_cover` vanishes there, given the margins `Lβ ≤ Tα` and `Tγ + w_k β ≤ Hβ` for every scale
`k < B` (`T = R! G`, `β = b₀ + 1`). -/
theorem block_out (wb : PTm 2) {c B K0 M R G α γ b0 L H : PTm n}
    (hL : Γ ⊢[PRAAx] le (L * succ b0) (fact R * G * α))
    (hH : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift B) ⟶
      le (fact (Syn.shift R) * Syn.shift G * Syn.shift γ +
          inst2 wb (var 0) (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G) (Syn.shift α) (Syn.shift γ)
            (Syn.shift b0)) * succ (Syn.shift b0))
        (Syn.shift H * succ (Syn.shift b0))))
    (hc : Γ ⊢[PRAAx] lt c L ⋎ le H c) :
    Γ ⊢[PRAAx] sg (inst2 (oB (bB wb)) c (pairT B (Xt K0 M R G α γ b0))) ≐ zero := by
  let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift B) :: Γ.map Fm.shift
  have hs : Γ ⊢[PRAAx] le (ap2 (sumF (rowB (bB wb))) B (pairT c (Xt K0 M R G α γ b0))) (B * zero) := by
    refine sum_le_const (rowB (bB wb)) (.allI (.impI ?_))
    rw [show Syn.shift (pairT c (Xt K0 M R G α γ b0)) = pairT (Syn.shift c)
        (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G) (Syn.shift α) (Syn.shift γ) (Syn.shift b0)) by
          simp [Syn.shift, Xt],
      inst2_rowB, show Syn.shift (zero : PTm n) = zero by simp [Syn.shift]]
    have ec := congrInst3 (Γ := Θ) (bB wb)
      (fst_pair (Syn.shift c) (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G) (Syn.shift α) (Syn.shift γ)
        (Syn.shift b0))) (.eqRefl (var 0))
      (snd_pair (Syn.shift c) (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G) (Syn.shift α) (Syn.shift γ)
        (Syn.shift b0)))
    have eb := b_at (Γ := Θ) wb (Syn.shift c) (var 0) (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G)
      (Syn.shift α) (Syn.shift γ) (Syn.shift b0)
    have hk := Prf.impE (hH.allOpen.wk (ψ := lt (var 0) (Syn.shift B))) Prf.hyp0
    have hL0 : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift L * succ (Syn.shift b0))
        (fact (Syn.shift R) * Syn.shift G * Syn.shift α) := by
      simpa [Fm.shift, Syn.shift] using hL.shift
    have hc0 : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift c) (Syn.shift L) ⋎ le (Syn.shift H) (Syn.shift c) := by
      simpa [Fm.shift, Syn.shift] using hc.shift
    have hL' : Θ ⊢[PRAAx] le (Syn.shift L * succ (Syn.shift b0)) (fact (Syn.shift R) * Syn.shift G * Syn.shift α) :=
      hL0.wk
    have hc' : Θ ⊢[PRAAx] lt (Syn.shift c) (Syn.shift L) ⋎ le (Syn.shift H) (Syn.shift c) := hc0.wk
    have hβ : Θ ⊢[PRAAx] succ (Syn.shift b0) ≐ succ (pred (succ (Syn.shift b0))) := congrSucc (pred_succ _).eqSymm
    have z := scale_out (c := Syn.shift c) (K := Kk (Syn.shift K0) (Syn.shift M) (var 0)) (M := Syn.shift M)
      (Q' := quo (Qk (Syn.shift K0) (var 0)) (num 4)) hβ hL' hk hc'
    exact (monus_zero _).eqTrans (ec.eqTrans (eb.eqTrans z))
  have h0 : Γ ⊢[PRAAx] le (B * zero) zero := by ipra_le 0
  have hz : Γ ⊢[PRAAx] ap2 (sumF (rowB (bB wb))) B (pairT c (Xt K0 M R G α γ b0)) ≐ zero :=
    (monus_zero _).eqSymm.eqTrans (le_trans hs h0)
  have e1 : Γ ⊢[PRAAx] inst2 (oB (bB wb)) c (pairT B (Xt K0 M R G α γ b0)) ≐
      ap2 (sumF (rowB (bB wb))) B (pairT c (Xt K0 M R G α γ b0)) := by
    rw [inst2_oB]
    exact congrAp2 (sumF (rowB (bB wb))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))
  exact (congrSg' (e1.eqTrans hz)).eqTrans sg_zero

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockLocal
