import IPRADerivations.Foundations.InjectionCount
import IPRADerivations.Foundations.IntervalPacking
import IPRADerivations.AnalyticNumberTheory.SumReindex

/-!
# Separated points in a window

Framework (packet `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, (K9): "Separation at
scale `ℓ` bounds the number of such centers by `(|I| + 2r_ℓ)4^ℓ + 1`"; reusable for any packing count).

A family of grid points `A_i`, `i < N`, with activity bits `act_i`, whose active members are pairwise
`s`-separated (`A_i + s ≤ A_j` or `A_j + s ≤ A_i`, `s ≥ 1`) and lie in the window `[a, a + λ]`, has at most
`⌊λ/s⌋ + 1` active members (`sep_count`):

  `Σ_{i<N} [act_i] ≤ ⌊λ/s⌋ + 1`.

The proof applies `InjectionCount.injection_count` to `i ↦ ⌊(A_i − a)/s⌋ < ⌊λ/s⌋ + 1`: two active members
in one cell would be closer than `s` (`coll_pt`), and every active member's cell is in range (`viol_pt`).
The hypotheses are schematic and pointwise (in the style of `Foundations/PackingPointwise`), as implications
from the activity bits.
-/

namespace LeanProofs.IPRA.Foundations.SeparatedCount

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (sg_bit)
open LeanProofs.IPRA.Topology.StaggeredGrids (eqb01' eq_of_eqb)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (le_quo_of_mul_le)
open LeanProofs.IPRA.Foundations.InjectionCount (clB inst2_clB rowCB inst2_rowCB coll vB inst2_vB viol sgB
  inst2_sgB injection_count)
open LeanProofs.IPRA.Foundations.IntervalPacking (acB absurd_one_zero')
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Pointwise -/

/-- Two active members do not share a cell. -/
theorem coll_pt {s a Ai Aj ci cj : PTm n} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s))
    (hsep : Γ ⊢[PRAAx] (sg ci ≐ one) ⟶ ((sg cj ≐ one) ⟶
      ((le a Ai ⋏ le a Aj) ⋏ (le (Ai + s) Aj ⋎ le (Aj + s) Ai)))) :
    Γ ⊢[PRAAx] sg ci * sg cj * eqb (quo (monus Ai a) s) (quo (monus Aj a) s) ≐ zero := by
  refine .orE (sg_bit (Γ := Γ) ci) ?_ ?_
  · exact (congrMul (congrMul Prf.hyp0 (.eqRefl _)) (.eqRefl _)).eqTrans
      ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _))
  · let Δ1 : List (Fm PTm n) := (sg ci ≐ one) :: Γ
    refine .orE (sg_bit (Γ := Δ1) cj) ?_ ?_
    · exact (congrMul (congrMul (.eqRefl _) Prf.hyp0) (.eqRefl _)).eqTrans
        ((congrMul (mul_zero _) (.eqRefl _)).eqTrans (zero_mul _))
    · let Δ2 : List (Fm PTm n) := (sg cj ≐ one) :: Δ1
      refine .orE (eqb01' (Γ := Δ2) (quo (monus Ai a) s) (quo (monus Aj a) s)) ?_ ?_
      · exact (congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)
      · let Θ : List (Fm PTm n) := (eqb (quo (monus Ai a) s) (quo (monus Aj a) s) ≐ one) :: Δ2
        have f : Θ ⊢[PRAAx] (le a Ai ⋏ le a Aj) ⋏ (le (Ai + s) Aj ⋎ le (Aj + s) Ai) :=
          .impE (.impE hsep.wk.wk.wk hyp2) Prf.hyp1
        have hsΘ : Θ ⊢[PRAAx] s ≐ succ (pred s) := hs.wk.wk.wk
        have pE := eq_of_eqb (Prf.hyp0 : Θ ⊢[PRAAx] eqb (quo (monus Ai a) s) (quo (monus Aj a) s) ≐ one)
        have pAi := eq_add_of_le (Prf.andE₁ (Prf.andE₁ f))
        have pAj := eq_add_of_le (Prf.andE₂ (Prf.andE₁ f))
        have di := div_mod_at (Γ := Θ) (x := monus Ai a) hsΘ
        have dj := div_mod_at (Γ := Θ) (x := monus Aj a) hsΘ
        have pdi := Prf.andE₁ di
        have pdj := Prf.andE₁ dj
        have hri : Θ ⊢[PRAAx] lt (rem (monus Ai a) s) s := Prf.andE₂ di
        have hrj : Θ ⊢[PRAAx] lt (rem (monus Aj a) s) s := Prf.andE₂ dj
        refine .orE (Prf.andE₂ f) ?_ ?_
        · let Θ' : List (Fm PTm n) := le (Ai + s) Aj :: Θ
          have h1 : Θ' ⊢[PRAAx] le (Ai + s) Aj := Prf.hyp0
          have hrj' : Θ' ⊢[PRAAx] lt (rem (monus Aj a) s) s := hrj.wk
          have e := natEq (pE.wk : Θ' ⊢[PRAAx] _)
          have eAi := natEq (pAi.wk : Θ' ⊢[PRAAx] _)
          have eAj := natEq (pAj.wk : Θ' ⊢[PRAAx] _)
          have edi := natEq (pdi.wk : Θ' ⊢[PRAAx] _)
          have edj := natEq (pdj.wk : Θ' ⊢[PRAAx] _)
          have hz : Θ' ⊢[PRAAx] le one zero := by
            ipra_le sl h1 + sl hrj' + 𝔞 (rem (monus Ai a) s) with eAj - eAi + edj - edi - 𝔞 s * e
          exact absurd_one_zero' ((monus_zero _).eqSymm.eqTrans hz)
        · let Θ' : List (Fm PTm n) := le (Aj + s) Ai :: Θ
          have h1 : Θ' ⊢[PRAAx] le (Aj + s) Ai := Prf.hyp0
          have hri' : Θ' ⊢[PRAAx] lt (rem (monus Ai a) s) s := hri.wk
          have e := natEq (pE.wk : Θ' ⊢[PRAAx] _)
          have eAi := natEq (pAi.wk : Θ' ⊢[PRAAx] _)
          have eAj := natEq (pAj.wk : Θ' ⊢[PRAAx] _)
          have edi := natEq (pdi.wk : Θ' ⊢[PRAAx] _)
          have edj := natEq (pdj.wk : Θ' ⊢[PRAAx] _)
          have hz : Θ' ⊢[PRAAx] le one zero := by
            ipra_le sl h1 + sl hri' + 𝔞 (rem (monus Aj a) s) with eAi - eAj + edi - edj + 𝔞 s * e
          exact absurd_one_zero' ((monus_zero _).eqSymm.eqTrans hz)

/-- An active member's cell is below `⌊λ/s⌋ + 1`. -/
theorem viol_pt {s a lam Ai ci : PTm n} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s))
    (hw : Γ ⊢[PRAAx] (sg ci ≐ one) ⟶ (le a Ai ⋏ le Ai (a + lam))) :
    Γ ⊢[PRAAx] sg ci * monus one (monus (succ (quo lam s)) (quo (monus Ai a) s)) ≐ zero := by
  refine .orE (sg_bit (Γ := Γ) ci) ?_ ?_
  · exact (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
  · let Θ : List (Fm PTm n) := (sg ci ≐ one) :: Γ
    have f : Θ ⊢[PRAAx] le a Ai ⋏ le Ai (a + lam) := .impE hw.wk Prf.hyp0
    have hsΘ : Θ ⊢[PRAAx] s ≐ succ (pred s) := hs.wk
    have eAi := natEq (eq_add_of_le (Prf.andE₁ f))
    have hle : Θ ⊢[PRAAx] le Ai (a + lam) := Prf.andE₂ f
    have di := div_mod_at (Γ := Θ) (x := monus Ai a) hsΘ
    have edi := natEq (Prf.andE₁ di)
    have hsg : Θ ⊢[PRAAx] le (s * quo (monus Ai a) s) lam := by
      ipra_le sl hle + 𝔞 (rem (monus Ai a) s) with eAi + edi
    have hgq : Θ ⊢[PRAAx] le (quo (monus Ai a) s) (quo lam s) := le_quo_of_mul_le hsΘ hsg
    have hlt : Θ ⊢[PRAAx] lt (quo (monus Ai a) s) (succ (quo lam s)) := by ipra_le sl hgq
    have e2 := natEq (eq_add_of_le (le_trans (le_succ_self _) hlt))
    have hp : Θ ⊢[PRAAx] le one (monus (succ (quo lam s)) (quo (monus Ai a) s)) := by ipra_le sl hlt with e2
    exact (congrMul Prf.hyp0 hp).eqTrans (mul_zero _)

/-! ## The count -/

section Count

variable (A act : PTm 2)

/-- `act_i` read from `X = ⟨a, ⟨s, y⟩⟩`. -/
def cK : PTm 2 := Syn.subst ![var 0, sndT (sndT (var 1))] act
/-- The cell `⌊(A_i − a)/s⌋`. -/
def gK : PTm 2 := quo (monus (Syn.subst ![var 0, sndT (sndT (var 1))] A) (fstT (var 1))) (fstT (sndT (var 1)))

theorem sub_ss (f : PTm 2) (i X : PTm n) :
    Syn.subst ![i, X] (Syn.subst ![var 0, sndT (sndT (var 1))] f) = inst2 f i (sndT (sndT X)) := by
  simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp

theorem inst2_cK (i X : PTm n) : inst2 (cK act) i X = inst2 act i (sndT (sndT X)) := by
  simp only [cK]; exact sub_ss act i X

theorem inst2_gK (i X : PTm n) :
    inst2 (gK A) i X = quo (monus (inst2 A i (sndT (sndT X))) (fstT X)) (fstT (sndT X)) := by
  simp only [gK, inst2, subst_ap2, PTm.subst_monus, subst_fstT, subst_sndT]
  rw [show Syn.subst ![i, X] (Syn.subst ![var 0, sndT (sndT (var 1))] A) = Syn.subst ![i, sndT (sndT X)] A from
    sub_ss A i X]
  simp

/-- Projections of `⟨a, ⟨s, y⟩⟩`. -/
theorem projX (a s y : PTm n) :
    (Γ ⊢[PRAAx] fstT (pairT a (pairT s y)) ≐ a) ∧ (Γ ⊢[PRAAx] fstT (sndT (pairT a (pairT s y))) ≐ s) ∧
      (Γ ⊢[PRAAx] sndT (sndT (pairT a (pairT s y))) ≐ y) :=
  ⟨fst_pair _ _, (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _), (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)⟩

/-- Separated active points in `[a, a + λ]` number at most `⌊λ/s⌋ + 1`. -/
theorem sep_count {N a s lam y : PTm n} (hs : Γ ⊢[PRAAx] s ≐ succ (pred s))
    (hsep : ∀ (Δ : List (Fm PTm (n + 1 + 1))) (i j : PTm (n + 1 + 1)), (Γ.map Fm.shift).map Fm.shift ⊆ Δ →
      (Δ ⊢[PRAAx] lt i j) → (Δ ⊢[PRAAx] lt j (Syn.shift (Syn.shift N))) →
      (Δ ⊢[PRAAx] (sg (inst2 act i (Syn.shift (Syn.shift y))) ≐ one) ⟶
        ((sg (inst2 act j (Syn.shift (Syn.shift y))) ≐ one) ⟶
          ((le (Syn.shift (Syn.shift a)) (inst2 A i (Syn.shift (Syn.shift y))) ⋏
              le (Syn.shift (Syn.shift a)) (inst2 A j (Syn.shift (Syn.shift y)))) ⋏
            (le (inst2 A i (Syn.shift (Syn.shift y)) + Syn.shift (Syn.shift s)) (inst2 A j (Syn.shift (Syn.shift y))) ⋎
              le (inst2 A j (Syn.shift (Syn.shift y)) + Syn.shift (Syn.shift s)) (inst2 A i (Syn.shift (Syn.shift y))))))))
    (hwin : ∀ (Δ : List (Fm PTm (n + 1))) (i : PTm (n + 1)), Γ.map Fm.shift ⊆ Δ →
      (Δ ⊢[PRAAx] lt i (Syn.shift N)) →
      (Δ ⊢[PRAAx] (sg (inst2 act i (Syn.shift y)) ≐ one) ⟶
        (le (Syn.shift a) (inst2 A i (Syn.shift y)) ⋏ le (inst2 A i (Syn.shift y)) (Syn.shift a + Syn.shift lam)))) :
    Γ ⊢[PRAAx] le (ap2 (sumF (acB act)) N y) (succ (quo lam s)) := by
  have hs1 : Γ.map Fm.shift ⊢[PRAAx] Syn.shift s ≐ succ (pred (Syn.shift s)) := by
    simpa [Fm.shift, Syn.shift] using hs.shift
  have hs2 : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] Syn.shift (Syn.shift s) ≐ succ (pred (Syn.shift (Syn.shift s))) := by
    simpa [Fm.shift, Syn.shift] using hs1.shift
  have hX1 : Syn.shift (pairT a (pairT s y)) = pairT (Syn.shift a) (pairT (Syn.shift s) (Syn.shift y)) := by
    simp only [shift_pairT]
  refine le_congr ?_ (.eqRefl _) (injection_count (cK act) (gK A) (N := N) (R := succ (quo lam s))
    (x := pairT a (pairT s y)) ?_ ?_)
  · -- the counted bits are the activity bits
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_sgB, inst2_sgB, inst2_cK, hX1]
    exact congrSg (congrInst2 act (.eqRefl _) (projX _ _ _).2.2)
  · -- no collisions
    refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
    rw [inst2_rowCB, hX1]
    let Θ₁ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    have hK1 : Θ₁ ⊢[PRAAx] lt (var 0) (Syn.shift N) := Prf.hyp0
    refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
    rw [inst2_clB, show Syn.shift (pairT (var 0 : PTm (n + 1)) (pairT (Syn.shift a) (pairT (Syn.shift s) (Syn.shift y)))) =
      pairT (var 1) (pairT (Syn.shift (Syn.shift a)) (pairT (Syn.shift (Syn.shift s)) (Syn.shift (Syn.shift y)))) by
        simp [Syn.shift]]
    let Θ₂ : List (Fm PTm (n + 1 + 1)) := lt (var 0) (Syn.shift (var 0)) :: Θ₁.map Fm.shift
    have hab : Θ₂ ⊢[PRAAx] lt (var 0) (var 1) := Prf.hyp0
    have hbK : Θ₂ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift N)) := by
      have s0 : Θ₁.map Fm.shift ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift N)) := by
        simpa [Fm.shift, Syn.shift] using hK1.shift
      exact s0.wk
    have hsub : (Γ.map Fm.shift).map Fm.shift ⊆ Θ₂ :=
      List.subset_cons_of_subset _ (List.subset_cons_of_subset _ (List.Subset.refl _))
    have hcore := coll_pt (hs2.weaken hsub) (hsep Θ₂ (var 0) (var 1) hsub hab hbK)
    refine .eqTrans ?_ hcore
    have hz := (fst_pair (Γ := Θ₂) (var 1) (pairT (Syn.shift (Syn.shift a)) (pairT (Syn.shift (Syn.shift s))
      (Syn.shift (Syn.shift y)))))
    have hX := snd_pair (Γ := Θ₂) (var 1) (pairT (Syn.shift (Syn.shift a)) (pairT (Syn.shift (Syn.shift s))
      (Syn.shift (Syn.shift y))))
    obtain ⟨pa, ps, py⟩ := projX (Γ := Θ₂) (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift s)) (Syn.shift (Syn.shift y))
    rw [inst2_cK, inst2_cK, inst2_gK, inst2_gK]
    have ey := (congrSnd (congrSnd hX)).eqTrans py
    have ea := (congrFst hX).eqTrans pa
    have es := (congrFst (congrSnd hX)).eqTrans ps
    exact congrMul (congrMul (congrSg (congrInst2 act (.eqRefl _) ey)) (congrSg (congrInst2 act hz ey)))
      (congrEqb' (congrAp2 quoF (congrMonus (congrInst2 A (.eqRefl _) ey) ea) es)
        (congrAp2 quoF (congrMonus (congrInst2 A hz ey) ea) es))
  · -- every active cell is in range
    refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
    rw [inst2_vB, show Syn.shift (pairT (succ (quo lam s)) (pairT a (pairT s y))) =
      pairT (succ (quo (Syn.shift lam) (Syn.shift s))) (pairT (Syn.shift a) (pairT (Syn.shift s) (Syn.shift y))) by
        simp [Syn.shift]]
    let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
    have hsub : Γ.map Fm.shift ⊆ Θ := List.subset_cons_of_subset _ (List.Subset.refl _)
    have hcore := viol_pt (hs1.weaken hsub) (hwin Θ (var 0) hsub Prf.hyp0)
    refine .eqTrans ?_ hcore
    have hR := fst_pair (Γ := Θ) (succ (quo (Syn.shift lam) (Syn.shift s)))
      (pairT (Syn.shift a) (pairT (Syn.shift s) (Syn.shift y)))
    have hX := snd_pair (Γ := Θ) (succ (quo (Syn.shift lam) (Syn.shift s)))
      (pairT (Syn.shift a) (pairT (Syn.shift s) (Syn.shift y)))
    obtain ⟨pa, ps, py⟩ := projX (Γ := Θ) (Syn.shift a) (Syn.shift s) (Syn.shift y)
    rw [inst2_cK, inst2_gK]
    have ey := (congrSnd (congrSnd hX)).eqTrans py
    have ea := (congrFst hX).eqTrans pa
    have es := (congrFst (congrSnd hX)).eqTrans ps
    exact congrMul (congrSg (congrInst2 act (.eqRefl _) ey))
      (congrMonus (.eqRefl _) (congrMonus hR (congrAp2 quoF (congrMonus (congrInst2 A (.eqRefl _) ey) ea) es)))

end Count

end LeanProofs.IPRA.Foundations.SeparatedCount
