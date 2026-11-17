import IPRADerivations.Probability.Histogram
import IPRADerivations.Probability.SignedParts
import IPRADerivations.Core.BlockSum

/-!
# Joint LOTUS and componentwise expectation

Packet: `probability/expected_value_ipra_2026-11-16`, Corollary `cor:multi-lotus` and Theorem
`thm:componentwise`.

* `code_eqb`: mixed-radix codes separate coordinates: for `v < K`,
  `[u K + v = j] = [u = ⌊j/K⌋] · [v = j mod K]`;
* `multi_lotus` (`cor:multi-lotus`, two observables): for `X₁ < n₁`, `X₂ < K` on outcomes,
  `∑_{i<M} w_i g(X₁(i), X₂(i)) = ∑_{a<n₁} ∑_{b<K} g(a, b) ∑_{i<M} w_i [X₁(i) = a] [X₂(i) = b]`,
  i.e. `E[g(X₁, X₂)] = ∑_{a,b} g(a, b) P(X₁ = a, X₂ = b)`. The pair is coded as `σ = X₁ K + X₂`, the
  finite LOTUS (`Histogram.lotus_bounded`) is applied to `σ`, and the code sum over `j < n₁ K` is
  flattened back to the nested sum (`BlockSum.flatten`); more observables iterate the coding;
* `componentwise` (`thm:componentwise`): for a vector observable `X_k(i)` and a fixed matrix
  `A(c, k)`, each coordinate of `E[A X]` is `∑_k A(c, k) E[X_k]` (coordinates are projections, and
  `SignedParts.finite_linearity` at the parameter `⟨c, x⟩`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.JointLotus

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.Expectation (Ew inst2_mul' inst2_add')
open LeanProofs.IPRA.Probability.Lotus (rB vB gσ inst2_gσ inst2_rB inst2_vB)
open LeanProofs.IPRA.Probability.Histogram (lotus_bounded)
open LeanProofs.IPRA.Probability.SignedParts (sbq inst2_sbq lcB wXB finite_linearity)
open LeanProofs.IPRA.Probability.Independence (shift_inst2)
open LeanProofs.IPRA.BlockSum (flatB flat_at flatten qr_block)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Mixed-radix codes -/

/-- From `u K + v = j` with `v < K`: `⌊j/K⌋ = u`, `j mod K = v`. -/
theorem code_inv {u v j K : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) (hv : Γ ⊢[PRAAx] lt v K)
    (e : Γ ⊢[PRAAx] u * K + v ≐ j) : Γ ⊢[PRAAx] (quo j K ≐ u) ⋏ (rem j K ≐ v) := by
  have q := qr_block (i := u) hK hv
  exact .andI ((congrAp2 quoF e.eqSymm (.eqRefl _)).eqTrans (Prf.andE₁ q))
    ((congrAp2 remF e.eqSymm (.eqRefl _)).eqTrans (Prf.andE₂ q))

/-- `j = ⌊j/K⌋ K + j mod K` and `j mod K < K` for `K ≥ 1`. -/
theorem code_split (j : PTm n) {K : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) :
    Γ ⊢[PRAAx] (quo j K * K + rem j K ≐ j) ⋏ lt (rem j K) K := by
  have d := div_mod (Γ := Γ) j (pred K)
  have q : Γ ⊢[PRAAx] quo j K ≐ quo j (succ (pred K)) := congrAp2 quoF (.eqRefl _) hK
  have r : Γ ⊢[PRAAx] rem j K ≐ rem j (succ (pred K)) := congrAp2 remF (.eqRefl _) hK
  refine .andI ?_ (lt_congr r.eqSymm hK.eqSymm (Prf.andE₂ d))
  have a := natEq (Prf.andE₁ d); have b := natEq q; have c := natEq r; have k := natEq hK
  apply deriveNat; ipra_simps
  linear_combination -a + 𝔞 (quo j (succ (pred K))) * k + 𝔞 K * b + c

theorem one_ne_zero' {φ : Fm PTm n} (h : Γ ⊢[PRAAx] (one : PTm n) ≐ zero) : Γ ⊢[PRAAx] φ :=
  .botE _ (succ_ne_zero h)

/-- `[u K + v = j] = [u = ⌊j/K⌋] [v = j mod K]` for `v < K`. -/
theorem code_eqb {u v j K : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) (hv : Γ ⊢[PRAAx] lt v K) :
    Γ ⊢[PRAAx] eqb (u * K + v) j ≐ eqb u (quo j K) * eqb v (rem j K) := by
  refine .orE (eqb_cases u (quo j K)) ?_ ?_
  · -- `u ≠ ⌊j/K⌋`: both sides vanish.
    let C := (eqb u (quo j K) ≐ zero) :: Γ
    refine .eqTrans ?_ ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)).eqSymm
    refine .orE (eqb_cases (u * K + v) j) Prf.hyp0 ?_
    have inv := code_inv (Γ := (eqb (u * K + v) j ≐ one) :: C) hK.wk.wk hv.wk.wk (eq_of_eqb Prf.hyp0)
    exact one_ne_zero' ((eqb_of_eq (Prf.andE₁ inv).eqSymm).eqSymm.eqTrans Prf.hyp1)
  · let C := (eqb u (quo j K) ≐ one) :: Γ
    have eu : C ⊢[PRAAx] u ≐ quo j K := eq_of_eqb Prf.hyp0
    refine .orE (eqb_cases v (rem j K)) ?_ ?_
    · let D := (eqb v (rem j K) ≐ zero) :: C
      refine .eqTrans ?_ ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)).eqSymm
      refine .orE (eqb_cases (u * K + v) j) Prf.hyp0 ?_
      have inv := code_inv (Γ := (eqb (u * K + v) j ≐ one) :: D) hK.wk.wk.wk hv.wk.wk.wk (eq_of_eqb Prf.hyp0)
      exact one_ne_zero' ((eqb_of_eq (Prf.andE₂ inv).eqSymm).eqSymm.eqTrans Prf.hyp1)
    · let D := (eqb v (rem j K) ≐ one) :: C
      have ev : D ⊢[PRAAx] v ≐ rem j K := eq_of_eqb Prf.hyp0
      have sp := code_split (Γ := D) j hK.wk.wk
      have e : D ⊢[PRAAx] u * K + v ≐ j :=
        (congrAdd (congrMul eu.wk (.eqRefl _)) ev).eqTrans (Prf.andE₁ sp)
      exact (eqb_of_eq e).eqTrans ((congrMul Prf.hyp1 Prf.hyp0).eqTrans (one_mul _)).eqSymm

/-! ## Bodies -/

section Bodies

variable (w X₁ X₂ : PTm 2) (g : PTm 3)

theorem inst2_eqb (f h : PTm 2) (i x : PTm n) : inst2 (eqb f h) i x = eqb (inst2 f i x) (inst2 h i x) := by
  simp [inst2]

/-- The code `σ(i, ⟨K, x⟩) = X₁(i, x) K + X₂(i, x)`. -/
abbrev cB : PTm 2 := sbq X₁ * fstT (var 1) + sbq X₂

theorem cB_at (i K x : PTm n) : Γ ⊢[PRAAx] inst2 (cB X₁ X₂) i (pairT K x) ≐ inst2 X₁ i x * K + inst2 X₂ i x := by
  rw [inst2_add', inst2_mul', inst2_sbq, inst2_sbq]
  have e : inst2 (fstT (var 1) : PTm 2) i (pairT K x) = fstT (pairT K x) := by simp [inst2]
  rw [e]
  exact congrAdd (congrMul (congrInst2 X₁ (.eqRefl _) (snd_pair _ _)) (fst_pair _ _))
    (congrInst2 X₂ (.eqRefl _) (snd_pair _ _))

/-- `g(X₁(i), X₂(i))`. -/
def gX : PTm 2 := Syn.subst ![X₁, X₂, var 1] g

theorem inst2_gX (i x : PTm n) : inst2 (gX X₁ X₂ g) i x = inst3 g (inst2 X₁ i x) (inst2 X₂ i x) x := by
  simp only [inst2, inst3, gX, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> rfl

/-- The joint weight body `w_i [X₁(i) = a] [X₂(i) = b]`, over `0 = i`, `1 = ⟨⟨a, b⟩, x⟩`. -/
abbrev JB : PTm 2 := sbq w * (eqb (sbq X₁) (fstT (fstT (var 1))) * eqb (sbq X₂) (sndT (fstT (var 1))))

theorem JB_at (i a b x : PTm n) :
    Γ ⊢[PRAAx] inst2 (JB w X₁ X₂) i (pairT (pairT a b) x) ≐
      inst2 w i x * (eqb (inst2 X₁ i x) a * eqb (inst2 X₂ i x) b) := by
  rw [inst2_mul', inst2_mul', inst2_eqb, inst2_eqb, inst2_sbq, inst2_sbq, inst2_sbq]
  have e1 : inst2 (fstT (fstT (var 1)) : PTm 2) i (pairT (pairT a b) x) = fstT (fstT (pairT (pairT a b) x)) := by
    simp [inst2]
  have e2 : inst2 (sndT (fstT (var 1)) : PTm 2) i (pairT (pairT a b) x) = sndT (fstT (pairT (pairT a b) x)) := by
    simp [inst2]
  rw [e1, e2]
  have s : Γ ⊢[PRAAx] sndT (pairT (pairT a b) x) ≐ x := snd_pair _ _
  exact congrMul (congrInst2 w (.eqRefl _) s) (congrMul
    (congrEqb (congrInst2 X₁ (.eqRefl _) s) ((congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)))
    (congrEqb (congrInst2 X₂ (.eqRefl _) s) ((congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _))))

/-- `T(a, b, ⟨M, x⟩) = g(a, b, x) ∑_{i<M} w_i [X₁(i) = a] [X₂(i) = b]`. -/
def TB : PTm 3 :=
  Syn.subst ![var 0, var 1, sndT (var 2)] g *
    ap2 (sumF (JB w X₁ X₂)) (fstT (var 2)) (pairT (pairT (var 0) (var 1)) (sndT (var 2)))

theorem inst3_TB (a b y : PTm n) :
    inst3 (TB w X₁ X₂ g) a b y =
      inst3 g a b (sndT y) * ap2 (sumF (JB w X₁ X₂)) (fstT y) (pairT (pairT a b) (sndT y)) := by
  simp only [inst3, TB, PTm.subst_mul, subst_ap2, subst_pairT, subst_fstT, subst_sndT, Syn.subst_subst,
    Syn.subst_var]
  congr 1
  congr 1; funext k; fin_cases k <;> simp

/-- The inner sums agree: `∑_{i<M} w_i [X₁ K + X₂ = j] = ∑_{i<M} w_i [X₁ = ⌊j/K⌋] [X₂ = j mod K]`. -/
theorem inner_eq {j M K x : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K))
    (h₂ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶ lt (inst2 X₂ (var 0) (Syn.shift x)) (Syn.shift K))) :
    Γ ⊢[PRAAx] ap2 (sumF (vB (sbq w) (cB X₁ X₂))) M (pairT j (pairT K x)) ≐
      ap2 (sumF (JB w X₁ X₂)) M (pairT (pairT (quo j K) (rem j K)) x) := by
  have hK' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift K ≐ succ (pred (Syn.shift K)) := by
    simpa [Fm.shift, Syn.shift] using hK.shift
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  have hq : Syn.shift (quo j K) = quo (Syn.shift j) (Syn.shift K) := by simp [Syn.shift]
  have hr : Syn.shift (rem j K) = rem (Syn.shift j) (Syn.shift K) := by simp [Syn.shift]
  rw [shift_pairT, shift_pairT, shift_pairT, shift_pairT, hq, hr, inst2_vB, inst2_sbq]
  refine .eqTrans ?_ (JB_at w X₁ X₂ _ _ _ _).eqSymm
  have s : (lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) ⊢[PRAAx] sndT (sndT (pairT (Syn.shift j) (pairT (Syn.shift K) (Syn.shift x)))) ≐ Syn.shift x :=
    (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
  refine congrMul (congrInst2 w (.eqRefl _) s) ?_
  refine (congrEqb ((congrInst2 _ (.eqRefl _) (snd_pair _ _)).eqTrans (cB_at X₁ X₂ _ _ _)) (fst_pair _ _)).eqTrans ?_
  exact code_eqb hK'.wk (Prf.impE h₂.allOpen.wk Prf.hyp0)

end Bodies

/-! ## The joint LOTUS -/

/-- `cor:multi-lotus` for two observables: if `X₁(i) < n₁` and `X₂(i) < K` (`K ≥ 1`) for `i < M`, then
`∑_{i<M} w_i g(X₁(i), X₂(i)) = ∑_{a<n₁} ∑_{b<K} g(a, b) ∑_{i<M} w_i [X₁(i) = a] [X₂(i) = b]`. -/
theorem multi_lotus (w X₁ X₂ : PTm 2) (g : PTm 3) {M n₁ K x : PTm n} (hK : Γ ⊢[PRAAx] K ≐ succ (pred K))
    (h₁ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶ lt (inst2 X₁ (var 0) (Syn.shift x)) (Syn.shift n₁)))
    (h₂ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶ lt (inst2 X₂ (var 0) (Syn.shift x)) (Syn.shift K))) :
    Γ ⊢[PRAAx] Ew w (gX X₁ X₂ g) M x ≐ ap2 (sumF (oB (TB w X₁ X₂ g))) n₁ (pairT K (pairT M x)) := by
  have hK' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift K ≐ succ (pred (Syn.shift K)) := by
    simpa [Fm.shift, Syn.shift] using hK.shift
  -- Step 1: rewrite the integrand through the code.
  have s1 : Γ ⊢[PRAAx] Ew w (gX X₁ X₂ g) M x ≐ ap2 (sumF (sbq w * gσ (cB X₁ X₂) (flatB g))) M (pairT K x) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT, inst2_mul', inst2_mul', inst2_sbq, inst2_gσ, inst2_gX]
    have c := cB_at (Γ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift) X₁ X₂ (var 0) (Syn.shift K) (Syn.shift x)
    have inv := code_inv (u := inst2 X₁ (var 0) (Syn.shift x)) hK'.wk (Prf.impE h₂.allOpen.wk Prf.hyp0) (.eqRefl _)
    refine .eqSymm (congrMul (congrInst2 w (.eqRefl _) (snd_pair _ _)) ?_)
    refine ((congrInst2 _ c (.eqRefl _)).eqTrans (flat_at g _ _ _)).eqTrans ?_
    exact congrInst3 g (Prf.andE₁ inv) (Prf.andE₂ inv) (.eqRefl _)
  -- Step 2: the bounded LOTUS for the code `σ < n₁ K`.
  have hr : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      lt (inst2 (cB X₁ X₂) (var 0) (Syn.shift (pairT K x))) (Syn.shift (n₁ * K))) := by
    refine .allI (.impI ?_)
    have hm : Syn.shift (n₁ * K) = Syn.shift n₁ * Syn.shift K := by simp [Syn.shift]
    rw [shift_pairT, hm]
    refine lt_congr (cB_at X₁ X₂ _ _ _).eqSymm (.eqRefl _) ?_
    have a1 := natEq (eq_add_of_le (Prf.impE h₁.allOpen.wk Prf.hyp0))
    have a2 := natEq (eq_add_of_le (Prf.impE h₂.allOpen.wk Prf.hyp0))
    refine le_of_eq_add (d := monus (Syn.shift K) (succ (inst2 X₂ (var 0) (Syn.shift x))) +
      monus (Syn.shift n₁) (succ (inst2 X₁ (var 0) (Syn.shift x))) * Syn.shift K) ?_
    apply deriveNat; ipra_simps
    linear_combination 𝔞 (Syn.shift K) * a1 + a2
  have s2 := lotus_bounded (sbq w) (cB X₁ X₂) (flatB g) hr
  -- Step 3: identify the code sum with the flattened joint sum.
  have s3 : Γ ⊢[PRAAx] ap2 (sumF (rB (sbq w) (cB X₁ X₂) (flatB g))) (n₁ * K) (pairT M (pairT K x)) ≐
      ap2 (sumF (flatB (TB w X₁ X₂ g))) (n₁ * K) (pairT K (pairT M x)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    have h₂' : Γ.map Fm.shift ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (Syn.shift M)) ⟶
        lt (inst2 X₂ (var 0) (Syn.shift (Syn.shift x))) (Syn.shift (Syn.shift K))) := by
      simpa [Fm.shift, Syn.shift, Syn.subst_subst] using h₂.shift
    simp only [shift_pairT]
    rw [inst2_rB]
    refine .eqTrans ?_ (flat_at _ _ _ _).eqSymm
    rw [inst3_TB]
    have s : (lt (var 0) (Syn.shift (n₁ * K)) :: Γ.map Fm.shift) ⊢[PRAAx]
        sndT (pairT (Syn.shift M) (pairT (Syn.shift K) (Syn.shift x))) ≐ pairT (Syn.shift K) (Syn.shift x) :=
      snd_pair _ _
    refine congrMul (((congrInst2 _ (.eqRefl _) s).eqTrans (flat_at g _ _ _)).eqTrans
      (congrInst3 g (.eqRefl _) (.eqRefl _) (snd_pair _ _).eqSymm)) ?_
    refine (congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) s)).eqTrans ?_
    refine (inner_eq w X₁ X₂ hK'.wk h₂'.wk).eqTrans ?_
    exact (congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
  exact s1.eqTrans (s2.eqTrans (s3.eqTrans (flatten _ hK)))

/-! ## Componentwise expectation -/

/-- `thm:componentwise`: the `c`-th coordinate of `E[A X]` for a vector observable `X_k(i)` (`k < r`) and
a fixed matrix `A(c, k)` read from the parameter `⟨c, x⟩` is `∑_{k<r} A(c, k) E[X_k]`:
`∑_i w_i ∑_k A(c, k) X_k(i) = ∑_k A(c, k) ∑_i w_i X_k(i)`. -/
theorem componentwise (w A : PTm 2) (X : PTm 3) (M r c x : PTm n) :
    Γ ⊢[PRAAx] Ew (sbq w) (oB (lcB A X)) M (pairT r (pairT c x)) ≐
      ap2 (sumF (sbq A * pB (wXB w X))) r (pairT M (pairT c x)) :=
  finite_linearity w A X M r (pairT c x)

end LeanProofs.IPRA.Probability.JointLotus
