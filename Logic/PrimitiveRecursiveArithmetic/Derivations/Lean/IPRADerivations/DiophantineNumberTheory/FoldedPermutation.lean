import IPRADerivations.DiophantineNumberTheory.FoldedResidues
import IPRADerivations.DiophantineNumberTheory.EisensteinParity
import IPRADerivations.AnalyticNumberTheory.Totatives
import IPRADerivations.AnalyticNumberTheory.PowerResidue

/-!
# The folded residues form a permutation

Packet: `diophantine-number-theory/quadratic_reciprocity_ipra`, `quadratic_reciprocity.tex`, `eq:perm` (additive
half): for an odd `p = 2h + 1` and `gcd(p, a) = 1`,

  `Σ_{i=1}^{h} b_i = Σ_{i=1}^{h} i`,   `b_i = min(a i mod p, p − a i mod p)`.

The map `σ(i) = b_{i+1} − 1` on `[0, h)` has the inverse `τ(j) = b'_{j+1} − 1`, where `b'` is formed with
`a' = a⁻¹ mod p` (`FoldedResidues.comp` in both directions), so `Totatives.sum_perm` applies (`perm_sum`).
With the inverse of `AnalyticNumberTheory/PowerResidue` this gives the hypothesis of
`EisensteinParity.floor_parity`, hence

  `par (floorSum p a) = par N_p(a)`   for odd `p`, odd `a`, `gcd(p, a) = 1`                 (`floor_gauss_parity`),

where `N_p(a) = Σ_{i=1}^{h} [a i mod p > h]` is the count of Gauss's lemma.

Not derived: the multiplicative half of `eq:perm`, Gauss's lemma `eq:gauss` (`signBit p a = par N_p(a)`), Euler's
criterion, and therefore Eisenstein's lemma `eq:eisenstein` and the reciprocity law.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.FoldedPermutation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_lt' zero_lt')
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (lift3 at_pair shift_cop)
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sum_perm)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidue (inv inv_spec inv_cop)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gcd_comm_one)
open LeanProofs.IPRA.DiophantineNumberTheory.QuadraticReciprocityGoal (floorSum)
open LeanProofs.IPRA.DiophantineNumberTheory.FoldedResidues (fold fold_le fold_spec rem_pos comp)
open LeanProofs.IPRA.DiophantineNumberTheory.EisensteinParity (bB idB eB inst2_bB inst2_idB floor_parity)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The folded residue as a term and as bodies -/

/-- `b_{i+1} = fold p ((i + 1) a mod p)`. -/
abbrev bF (i p a : PTm n) : PTm n := fold p (rem (succ i * a) p)

/-- `b` over `0 = i`, `1 = p`, `2 = a`. -/
abbrev bF3 : PTm 3 := fold (var 1) (rem (succ (var 0) * var 2) (var 1))

theorem inst3_bF3 (i p a : PTm n) : inst3 bF3 i p a = bF i p a := by simp [inst3, subst_ap1]

theorem congrBF {i i' p p' a a' : PTm n} (h₁ : Γ ⊢[PRAAx] i ≐ i') (h₂ : Γ ⊢[PRAAx] p ≐ p')
    (h₃ : Γ ⊢[PRAAx] a ≐ a') : Γ ⊢[PRAAx] bF i p a ≐ bF i' p' a' := by
  have e := congrInst3 bF3 h₁ h₂ h₃
  rw [inst3_bF3 i p a, inst3_bF3 i' p' a'] at e
  exact e

/-- `fold p r` over `0 = r`, `1 = p`. -/
abbrev fold2 : PTm 2 := fold (var 1) (var 0)

theorem inst2_fold2 (r p : PTm n) : inst2 fold2 r p = fold p r := by simp [inst2, subst_ap1]

theorem congrFold {p r r' : PTm n} (h : Γ ⊢[PRAAx] r ≐ r') : Γ ⊢[PRAAx] fold p r ≐ fold p r' := by
  have e := congrInst2 fold2 h (.eqRefl p)
  rw [inst2_fold2 r p, inst2_fold2 r' p] at e
  exact e

/-- `σ(i) = b_{i+1}(a) − 1` over `0 = i`, `1 = ⟨p, ⟨a, a'⟩⟩`. -/
abbrev sB : PTm 2 :=
  pred (fold (fstT (var 1)) (rem (succ (var 0) * fstT (sndT (var 1))) (fstT (var 1))))
/-- `τ(j) = b_{j+1}(a') − 1`. -/
abbrev tB : PTm 2 :=
  pred (fold (fstT (var 1)) (rem (succ (var 0) * sndT (sndT (var 1))) (fstT (var 1))))

theorem inst2_sB (i x : PTm n) : inst2 sB i x = pred (bF i (fstT x) (fstT (sndT x))) := by
  simp [inst2, subst_ap1]

theorem inst2_tB (i x : PTm n) : inst2 tB i x = pred (bF i (fstT x) (sndT (sndT x))) := by
  simp [inst2, subst_ap1]

theorem s_at (i p a a' : PTm n) :
    Γ ⊢[PRAAx] inst2 sB i (pairT p (pairT a a')) ≐ pred (bF i p a) := by
  rw [inst2_sB]
  exact congrPred (congrBF (.eqRefl _) (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)))

theorem t_at (i p a a' : PTm n) :
    Γ ⊢[PRAAx] inst2 tB i (pairT p (pairT a a')) ≐ pred (bF i p a') := by
  rw [inst2_tB]
  exact congrPred (congrBF (.eqRefl _) (fst_pair _ _) ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)))

/-! ## Pointwise facts -/

theorem pred_lt {b h : PTm n} (hb : Γ ⊢[PRAAx] le b h) (hh : Γ ⊢[PRAAx] h ≐ succ (pred h)) :
    Γ ⊢[PRAAx] lt (pred b) h := by
  refine .orE (zero_or_succ b) ?_ ?_
  · exact lt_congr ((congrPred Prf.hyp0).eqTrans pred_zero).eqSymm (.eqRefl _) (zero_lt' hh.wk)
  · exact le_congr Prf.hyp0 (.eqRefl _) hb.wk

section Pointwise

variable {p a a' : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * half p + one)
include ep

/-- `b_{i+1} − 1 < h` for every `i`. -/
theorem b_range (hh : Γ ⊢[PRAAx] half p ≐ succ (pred (half p))) (i c : PTm n) :
    Γ ⊢[PRAAx] lt (pred (bF i p c)) (half p) := by
  have hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p) :=
    pos_of_eq_succ (c := two * half p) (ep.eqTrans (by apply deriveNat; ipra_simps; ring))
  exact pred_lt (fold_le ep (rem_lt' hp1 _)) hh

/-- `b_{i+1} ≥ 1` for `i < h` and `gcd(p, a) = 1`. -/
theorem b_pos {i : PTm n} (hc : Γ ⊢[PRAAx] gcd p a ≐ one) (hi : Γ ⊢[PRAAx] lt i (half p)) :
    Γ ⊢[PRAAx] bF i p a ≐ succ (pred (bF i p a)) := by
  have hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p) :=
    pos_of_eq_succ (c := two * half p) (ep.eqTrans (by apply deriveNat; ipra_simps; ring))
  exact Prf.andE₁ (fold_spec (rem_pos ep hc hi) (rem_lt' hp1 _))

/-- `τ(σ(i)) = i` for `i < h`: `b_{b_{i+1}(a)}(a') = i + 1`. -/
theorem round {i : PTm n} (hc : Γ ⊢[PRAAx] gcd p a ≐ one) (hinv : Γ ⊢[PRAAx] rem (a * a') p ≐ rem one p)
    (hi : Γ ⊢[PRAAx] lt i (half p)) : Γ ⊢[PRAAx] pred (bF (pred (bF i p a)) p a') ≐ i := by
  have c := comp ep hc hinv hi
  have e : Γ ⊢[PRAAx] bF (pred (bF i p a)) p a' ≐ fold p (rem (bF i p a * a') p) :=
    congrFold (congrAp2 remF (congrMul (b_pos ep hc hi).eqSymm (.eqRefl _)) (.eqRefl _))
  exact (congrPred (e.eqTrans c)).eqTrans (pred_succ _)

end Pointwise

/-! ## The permutation -/

/-- The three hypotheses of `Permutation.prod_perm` and `Totatives.sum_perm` for `σ` and `τ` on `[0, h)`:
range, `σ ∘ τ = id` and `τ ∘ σ = id`. -/
theorem perm_data {p a a' : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * half p + one)
    (hh : Γ ⊢[PRAAx] half p ≐ succ (pred (half p)))
    (hc : Γ ⊢[PRAAx] gcd p a ≐ one) (hc' : Γ ⊢[PRAAx] gcd p a' ≐ one)
    (hinv : Γ ⊢[PRAAx] rem (a * a') p ≐ rem one p) :
    (Γ ⊢[PRAAx] Permutation.rangeAll sB (half p) (pairT p (pairT a a'))) ∧
      (Γ ⊢[PRAAx] Permutation.invAll sB tB (half p) (pairT p (pairT a a'))) ∧
      (Γ ⊢[PRAAx] Permutation.retAll sB tB (half p) (pairT p (pairT a a'))) := by
  have hinv2 : Γ ⊢[PRAAx] rem (a' * a) p ≐ rem one p :=
    (congrAp2 remF (mul_comm _ _) (.eqRefl _)).eqTrans hinv
  have sH : Syn.shift (half p) = half (Syn.shift p) := by simp [Syn.shift, subst_ap1]
  have ep' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift p ≐ two * half (Syn.shift p) + one := by
    simpa [Fm.shift, Syn.shift, subst_ap1] using ep.shift
  have hh' : (Γ.map Fm.shift) ⊢[PRAAx] half (Syn.shift p) ≐ succ (pred (half (Syn.shift p))) := by
    simpa [Fm.shift, Syn.shift, subst_ap1] using hh.shift
  have hcS := shift_cop hc
  have hcS' := shift_cop hc'
  have hinvS : (Γ.map Fm.shift) ⊢[PRAAx]
      rem (Syn.shift a * Syn.shift a') (Syn.shift p) ≐ rem one (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hinv.shift
  have hinvS2 : (Γ.map Fm.shift) ⊢[PRAAx]
      rem (Syn.shift a' * Syn.shift a) (Syn.shift p) ≐ rem one (Syn.shift p) := by
    simpa [Fm.shift, Syn.shift] using hinv2.shift
  refine ⟨?_, ?_, ?_⟩
  · refine .allI ?_
    simp only [shift_pairT]
    rw [sH]
    exact lt_congr (s_at _ _ _ _).eqSymm (.eqRefl _) (b_range ep' hh' _ _)
  · refine .allI (.impI (.andI ?_ ?_))
    · simp only [shift_pairT]
      rw [sH]
      exact lt_congr (t_at _ _ _ _).eqSymm (.eqRefl _) (b_range ep'.wk hh'.wk _ _)
    · simp only [shift_pairT]
      rw [sH]
      refine (s_at _ _ _ _).eqTrans ?_
      exact (congrPred (congrBF (t_at _ _ _ _) (.eqRefl _) (.eqRefl _))).eqTrans
        (round ep'.wk hcS'.wk hinvS2.wk Prf.hyp0)
  · refine .allI (.impI ?_)
    simp only [shift_pairT]
    rw [sH]
    refine (t_at _ _ _ _).eqTrans ?_
    exact (congrPred (congrBF (s_at _ _ _ _) (.eqRefl _) (.eqRefl _))).eqTrans
      (round ep'.wk hcS.wk hinvS.wk Prf.hyp0)

/-- `b_{i+1} = σ(i) + 1` for `i < h`, as an identity of summands with the two parameters. -/
theorem b_eq_succ_s {p a a' i : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * half p + one)
    (hc : Γ ⊢[PRAAx] gcd p a ≐ one) (hi : Γ ⊢[PRAAx] lt i (half p)) :
    Γ ⊢[PRAAx] inst2 bB i (pairT p a) ≐ inst2 (Permutation.FS idB sB) i (pairT p (pairT a a')) := by
  rw [inst2_bB, Permutation.inst2_FS, inst2_idB]
  exact (congrBF (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans
    ((b_pos ep hc hi).eqTrans (congrSucc (s_at _ _ _ _)).eqSymm)

/-- `Σ_{i<h} b_{i+1} = Σ_{i<h} (i + 1)` for `p = 2h + 1`, `gcd(p, a) = gcd(p, a') = 1`, `a a' ≡ 1 (mod p)`. -/
theorem perm_sum {p a a' : PTm n} (ep : Γ ⊢[PRAAx] p ≐ two * half p + one)
    (hc : Γ ⊢[PRAAx] gcd p a ≐ one) (hc' : Γ ⊢[PRAAx] gcd p a' ≐ one)
    (hinv : Γ ⊢[PRAAx] rem (a * a') p ≐ rem one p) :
    Γ ⊢[PRAAx] ap2 (sumF bB) (half p) (pairT p a) ≐ ap2 (sumF idB) (half p) (pairT p a) := by
  refine .orE (zero_or_succ (half p)) ?_ ?_
  · exact (congrAp2 (sumF bB) Prf.hyp0 (.eqRefl _)).eqTrans ((sum_zero _ _).eqTrans
      ((congrAp2 (sumF idB) Prf.hyp0 (.eqRefl _)).eqTrans (sum_zero _ _)).eqSymm)
  · let C : List (Fm PTm n) := (half p ≐ succ (pred (half p))) :: Γ
    have epC : C ⊢[PRAAx] p ≐ two * half p + one := ep.wk
    have hcC : C ⊢[PRAAx] gcd p a ≐ one := hc.wk
    obtain ⟨hr, hi, ht⟩ := perm_data (a' := a') epC Prf.hyp0 hcC hc'.wk hinv.wk
    have sp := sum_perm (f := idB) hr hi ht
    have sH : Syn.shift (half p) = half (Syn.shift p) := by simp [Syn.shift, subst_ap1]
    have ep' : (C.map Fm.shift) ⊢[PRAAx] Syn.shift p ≐ two * half (Syn.shift p) + one := by
      simpa [Fm.shift, Syn.shift, subst_ap1] using epC.shift
    have hcS := shift_cop hcC
    have l : C ⊢[PRAAx] ap2 (sumF bB) (half p) (pairT p a) ≐
        ap2 (sumF (Permutation.FS idB sB)) (half p) (pairT p (pairT a a')) := by
      refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
      simp only [shift_pairT]
      rw [sH]
      exact b_eq_succ_s ep'.wk hcS.wk Prf.hyp0
    have r : C ⊢[PRAAx] ap2 (sumF idB) (half p) (pairT p (pairT a a')) ≐
        ap2 (sumF idB) (half p) (pairT p a) := by
      refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
      rw [inst2_idB, inst2_idB]
      exact .eqRefl _
    exact l.eqTrans (sp.eqTrans r)

/-! ## The parity of the floor sum is the parity of Gauss's count -/

/-- `Σ_{i<h} b_{i+1} = Σ_{i<h} (i + 1)` for odd `p`, `a ≥ 1` and `gcd(p, a) = 1`. -/
theorem perm_sum_inv {p a : PTm n} (hp : Γ ⊢[PRAAx] par p ≐ one) (ha1 : Γ ⊢[PRAAx] a ≐ succ (pred a))
    (hc : Γ ⊢[PRAAx] gcd p a ≐ one) :
    Γ ⊢[PRAAx] ap2 (sumF bB) (half p) (pairT p a) ≐ ap2 (sumF idB) (half p) (pairT p a) := by
  have ep := odd_of hp
  have hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p) :=
    pos_of_eq_succ (c := two * half p) (ep.eqTrans (by apply deriveNat; ipra_simps; ring))
  refine .orE (zero_or_succ (half p)) ?_ ?_
  · exact (congrAp2 (sumF bB) Prf.hyp0 (.eqRefl _)).eqTrans ((sum_zero _ _).eqTrans
      ((congrAp2 (sumF idB) Prf.hyp0 (.eqRefl _)).eqTrans (sum_zero _ _)).eqSymm)
  · let C : List (Fm PTm n) := (half p ≐ succ (pred (half p))) :: Γ
    have hh := natEq (Prf.hyp0 : C ⊢[PRAAx] half p ≐ succ (pred (half p)))
    have x := natEq (ep.wk : C ⊢[PRAAx] p ≐ two * half p + one)
    have hq : C ⊢[PRAAx] le two p := by
      refine le_of_eq_add (d := succ (two * pred (half p))) ?_
      apply deriveNat; ipra_simps
      linear_combination x + 2 * hh
    have hD : C ⊢[PRAAx] gcd a p ≐ one := gcd_comm_one ha1.wk hc.wk
    have hc' : C ⊢[PRAAx] gcd p (inv a p) ≐ one := gcd_comm_one hp1.wk (inv_cop hq hD)
    exact perm_sum ep.wk hc.wk hc' (inv_spec hq hD)

/-- `par (floorSum p a) = par N_p(a)` for odd `p`, odd `a` and `gcd(p, a) = 1`, where
`N_p(a) = Σ_{i<h} [(i + 1) a mod p > h]`. -/
theorem floor_gauss_parity {p a : PTm n} (hp : Γ ⊢[PRAAx] par p ≐ one) (ha : Γ ⊢[PRAAx] par a ≐ one)
    (hc : Γ ⊢[PRAAx] gcd p a ≐ one) :
    Γ ⊢[PRAAx] par (floorSum p a) ≐ par (ap2 (sumF eB) (half p) (pairT p a)) := by
  have ha1 : Γ ⊢[PRAAx] a ≐ succ (pred a) :=
    pos_of_eq_succ (c := two * half a) ((odd_of ha).eqTrans (by apply deriveNat; ipra_simps; ring))
  exact floor_parity hp ha (perm_sum_inv hp ha1 hc)

end LeanProofs.IPRA.DiophantineNumberTheory.FoldedPermutation
