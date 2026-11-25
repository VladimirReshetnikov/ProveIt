import IPRADerivations.AnalyticNumberTheory.MobiusFloor
import IPRADerivations.AnalyticNumberTheory.FactorialLambda
import IPRADerivations.AnalyticNumberTheory.SumReindex
import IPRADerivations.AnalyticNumberTheory.EulerProduct
import IPRADerivations.AnalyticNumberTheory.GcdFiber
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.Combinatorics.Stirling
import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.CertificateTactics

/-!
# The floor recurrence determines the Mertens function

Packet: `analytic-number-theory/mertens-ipra`, `identities.tex`, `thm:floor-recurrence`:

  "For `N ≥ 1`, `∑_{a=1}^{N} M(q_N(a)) = 1` … The recursion, together with `M(0) = 0`, uniquely determines `M`."
  Proof: "If two candidate tables obey the same equations through `N`, induction on the Boolean predicate that
  all entries through `t` agree gives equality through `N`."

A candidate table is a pair of bodies `g = g⁺ − g⁻` with natural values (as `M = M⁺ − M⁻` in `MobiusFloor`). The
recurrence at `s` is the equation `∑_{a ≤ s} [a ≥ 1] g⁺(⌊s/a⌋) = [s ≥ 1] + ∑_{a ≤ s} [a ≥ 1] g⁻(⌊s/a⌋)`, and "the
recurrence holds for all `s ≤ X`" is the quantifier-free equation `∑_{s ≤ X} err(s) = 0` (`errB`).

* `rowB`, `Sg`: the rows `[a ≥ 1] g(⌊s/a⌋)` and their sums;
* `split_two`: `∑_{a ≤ t} f(a) = f(0) + f(1) + ∑_{k < t − 1} f(2 + k)` for `t ≥ 1`; `sum_cross`: two sums against two
  sums, termwise;
* `tail_pt`: for `a = 2 + k ≤ t` the quotient `u = ⌊t/a⌋` has `1 ≤ u < t`, where the tables agree;
* `point`: if the tables agree below `t`, they agree at `t` (`1 ≤ t ≤ X`);
* `W_zero`: the count of disagreements below any `t` vanishes, by induction on `t` in the given context;
* **`mertens_unique`**: if `g` satisfies the recurrence for all `s ≤ X`, then `g⁺(t) + M⁻(t) = g⁻(t) + M⁺(t)`
  for `1 ≤ t ≤ X`, that is `g(t) = M(t)`;
* `mertens_err`: the Mertens function itself satisfies the hypothesis (`MobiusFloor.mertens_floor`).

The entry at `0` does not occur in any recurrence (`⌊s/a⌋ ≥ 1` for `1 ≤ a ≤ s`), so the condition `M(0) = 0` only
fixes that entry and is not needed for `t ≥ 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.MertensUnique

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (Bs bS)
open LeanProofs.IPRA.AnalyticNumberTheory.SymmetrySum (aPB aNB)
open LeanProofs.IPRA.AnalyticNumberTheory.MobiusFloor (MP MN GPB GNB inst2_GPB inst2_GNB mertens_floor)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (fB sB inst2_fB inst2_sB sum_add2)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (le_quo_of_mul_le)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eq_of_viol viol_of_eq)
open LeanProofs.IPRA.AnalyticNumberTheory.GcdFiber (div_eq)
open LeanProofs.IPRA.Combinatorics.Stirling (gle gle_of_le gle_above)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Rows of a table -/

/-- `[a ≥ 1] g(⌊s/a⌋, y)`, over `0 = a`, `1 = ⟨s, y⟩`. -/
def rowB (g : PTm 2) : PTm 2 := sg (var 0) * Syn.subst ![quo (fstT (var 1)) (var 0), sndT (var 1)] g

theorem inst2_rowB (g : PTm 2) (a z : PTm n) :
    inst2 (rowB g) a z = sg a * inst2 g (quo (fstT z) a) (sndT z) := by
  simp only [inst2, rowB, PTm.subst_mul, Syn.subst_subst]
  congr 1
  · simp
  · congr 1; funext j; fin_cases j <;> simp

theorem row_at (g : PTm 2) (a s y : PTm n) :
    Γ ⊢[PRAAx] inst2 (rowB g) a (pairT s y) ≐ sg a * inst2 g (quo s a) y := by
  rw [inst2_rowB]
  exact congrMul (.eqRefl _) (congrInst2 g (congrAp2 quoF (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))

/-- `∑_{a ≤ s} [a ≥ 1] g(⌊s/a⌋, y)`. -/
abbrev Sg (g : PTm 2) (s y : PTm n) : PTm n := ap2 (sumF (rowB g)) (succ s) (pairT s y)

/-- `M⁺` and `M⁻` as tables, over `0 = t`. -/
abbrev mPB : PTm 2 := ap2 (sumF (bS aPB)) (var 0) zero
abbrev mNB : PTm 2 := ap2 (sumF (bS aNB)) (var 0) zero

theorem inst2_mP (t y : PTm n) : inst2 mPB t y = MP t := by simp [inst2]
theorem inst2_mN (t y : PTm n) : inst2 mNB t y = MN t := by simp [inst2]

/-! ## Splitting and comparing sums -/

theorem two_add' (P : PTm n) : Γ ⊢[PRAAx] succ (succ P) ≐ two + P := by ipra_ring

theorem split_alg {S S2 S1 S0 T f0 f1 : PTm n} (s : Γ ⊢[PRAAx] S ≐ S2 + T) (h2 : Γ ⊢[PRAAx] S2 ≐ S1 + f1)
    (h1 : Γ ⊢[PRAAx] S1 ≐ S0 + f0) (h0 : Γ ⊢[PRAAx] S0 ≐ zero) : Γ ⊢[PRAAx] S ≐ f0 + f1 + T := by
  ipra_lc natEq s + natEq h2 + natEq h1 + natEq h0

/-- `∑_{a ≤ t} f(a) = f(0) + f(1) + ∑_{k < t − 1} f(2 + k)` for `t ≥ 1`. -/
theorem split_two (f : PTm 2) {t x : PTm n} (ht : Γ ⊢[PRAAx] t ≐ succ (pred t)) :
    Γ ⊢[PRAAx] ap2 (sumF f) (succ t) x ≐
      inst2 f zero x + inst2 f one x + ap2 (sumF (offB f)) (pred t) (pairT two x) := by
  have e : Γ ⊢[PRAAx] succ t ≐ two + pred t := (congrSucc ht).eqTrans (two_add' _)
  exact (congrAp2 (sumF f) e (.eqRefl _)).eqTrans
    (split_alg (sum_split f two (pred t) x) (sum_succ' f one x) (sum_succ' f zero x) (sum_zero f x))

/-- The term of the tail: `f(2 + k, x)`. -/
theorem off_two (f : PTm 2) (k x : PTm n) :
    Γ ⊢[PRAAx] inst2 (offB f) k (pairT two x) ≐ inst2 f (two + k) x := by
  rw [inst2_offB]
  exact congrInst2 f (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

/-- Termwise `f₁ + f₂ = f₃ + f₄` gives `∑ f₁ + ∑ f₂ = ∑ f₃ + ∑ f₄`. -/
theorem sum_cross (f1 f2 f3 f4 : PTm 2) {N x1 x2 x3 x4 : PTm n}
    (hp : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 f1 (var 0) (Syn.shift x1) + inst2 f2 (var 0) (Syn.shift x2) ≐
        inst2 f3 (var 0) (Syn.shift x3) + inst2 f4 (var 0) (Syn.shift x4)))) :
    Γ ⊢[PRAAx] ap2 (sumF f1) N x1 + ap2 (sumF f2) N x2 ≐ ap2 (sumF f3) N x3 + ap2 (sumF f4) N x4 := by
  have pt : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 (addBody (fB f1) (sB f2)) (var 0) (Syn.shift (pairT x1 x2)) ≐
        inst2 f1 (var 0) (Syn.shift x1) + inst2 f2 (var 0) (Syn.shift x2))) := by
    refine .allI (.impI ?_)
    rw [inst2_addBody, inst2_fB, inst2_sB, shift_pairT]
    exact congrAdd (congrInst2 f1 (.eqRefl _) (fst_pair _ _)) (congrInst2 f2 (.eqRefl _) (snd_pair _ _))
  have t1 := sum_add2 f1 f2 (addBody (fB f1) (sB f2)) (K := N) (x := x1) (x' := x2) (z := pairT x1 x2) pt
  have t2 := sum_add2 f3 f4 (addBody (fB f1) (sB f2)) (K := N) (x := x3) (x' := x4) (z := pairT x1 x2)
    (.allI (.impI ((Prf.impE pt.allOpen.wk Prf.hyp0).eqTrans (Prf.impE hp.allOpen.wk Prf.hyp0))))
  exact t1.eqSymm.eqTrans t2

/-! ## The hypothesis and the count of disagreements -/

/-- The error of the recurrence at `s`: `1 ∸ [∑_{a ≤ s} g⁺(⌊s/a⌋) = [s ≥ 1] + ∑_{a ≤ s} g⁻(⌊s/a⌋)]`, over `0 = s`,
`1 = y`. -/
def errB (gP gN : PTm 2) : PTm 2 :=
  monus one (eqb (ap2 (sumF (rowB gP)) (succ (var 0)) (pairT (var 0) (var 1)))
    (sg (var 0) + ap2 (sumF (rowB gN)) (succ (var 0)) (pairT (var 0) (var 1))))

theorem inst2_err (gP gN : PTm 2) (s y : PTm n) :
    inst2 (errB gP gN) s y = monus one (eqb (Sg gP s y) (sg s + Sg gN s y)) := by
  simp [inst2, errB]

/-- The disagreement at `s`: `[s ≥ 1][s ≤ X] (1 ∸ [g⁺(s) + M⁻(s) = g⁻(s) + M⁺(s)])`, over `0 = s`, `1 = ⟨X, y⟩`. -/
def vB (gP gN : PTm 2) : PTm 2 :=
  sg (var 0) * (gle (var 0) (fstT (var 1)) * monus one (eqb (sB gP + mNB) (sB gN + mPB)))

theorem inst2_v (gP gN : PTm 2) (s Y : PTm n) :
    inst2 (vB gP gN) s Y = sg s * (gle s (fstT Y) *
      monus one (eqb (inst2 gP s (sndT Y) + MN s) (inst2 gN s (sndT Y) + MP s))) := by
  have e : inst2 (vB gP gN) s Y = sg s * (gle s (fstT Y) *
      monus one (eqb (inst2 (sB gP) s Y + MN s) (inst2 (sB gN) s Y + MP s))) := by
    simp [inst2, vB]
  rw [e, inst2_sB, inst2_sB]

theorem v_at (gP gN : PTm 2) (s X y : PTm n) :
    Γ ⊢[PRAAx] inst2 (vB gP gN) s (pairT X y) ≐
      sg s * (gle s X * monus one (eqb (inst2 gP s y + MN s) (inst2 gN s y + MP s))) := by
  rw [inst2_v]
  exact congrMul (.eqRefl _) (congrMul (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (fst_pair _ _)))
    (congrMonus (.eqRefl _) (AnalyticNumberTheory.Euler.congrEqb
      (congrAdd (congrInst2 gP (.eqRefl _) (snd_pair _ _)) (.eqRefl _))
      (congrAdd (congrInst2 gN (.eqRefl _) (snd_pair _ _)) (.eqRefl _)))))

/-! ## The quotients `⌊t/a⌋` for `2 ≤ a ≤ t` -/

theorem a_le {t P k : PTm n} (ht : Γ ⊢[PRAAx] t ≐ succ P) (hk : Γ ⊢[PRAAx] lt k P) :
    Γ ⊢[PRAAx] le (two + k) t := by
  have x := natEq ht
  ipra_le sl hk with x

theorem lt_of_two {t a u : PTm n} (h1 : Γ ⊢[PRAAx] le (a * u) t) (ha : Γ ⊢[PRAAx] le two a)
    (hu : Γ ⊢[PRAAx] le one u) : Γ ⊢[PRAAx] lt u t := by
  ipra_le sl h1 + sl ha * 𝔞 u + sl hu

theorem two_add_pos (k : PTm n) : Γ ⊢[PRAAx] two + k ≐ succ (pred (two + k)) :=
  AnalyticNumberTheory.Primes.eq_succ_pred (y := succ k) (by ipra_ring)

theorem mul_one_r (a : PTm n) : Γ ⊢[PRAAx] a * one ≐ a := by ipra_ring

theorem bits0 {s b V : PTm n} (hs : Γ ⊢[PRAAx] s ≐ one) (hb : Γ ⊢[PRAAx] b ≐ one)
    (h : Γ ⊢[PRAAx] s * (b * V) ≐ zero) : Γ ⊢[PRAAx] V ≐ zero := by
  ipra_lc natEq h - 𝔞 b * 𝔞 V * natEq hs - 𝔞 V * natEq hb

theorem scale_eq {s A B C D : PTm n} (h : Γ ⊢[PRAAx] A + B ≐ C + D) :
    Γ ⊢[PRAAx] s * A + s * B ≐ s * C + s * D := by
  ipra_lc 𝔞 s * natEq h

/-- `[u ≥ 1] = 1` for `u ≥ 1`. -/
theorem sg_of_one_le {u : PTm n} (h : Γ ⊢[PRAAx] le one u) : Γ ⊢[PRAAx] sg u ≐ one :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_zero one)

/-- The tables agree at `u = ⌊t/(2 + k)⌋` when they agree below `t` (`k < t − 1`, `t ≤ X`). -/
theorem agree_quo (gP gN : PTm 2) {X y t k : PTm n}
    (hW : Γ ⊢[PRAAx] ap2 (sumF (vB gP gN)) t (pairT X y) ≐ zero) (ht : Γ ⊢[PRAAx] t ≐ succ (pred t))
    (htX : Γ ⊢[PRAAx] le t X) (hk : Γ ⊢[PRAAx] lt k (pred t)) :
    Γ ⊢[PRAAx] inst2 gP (quo t (two + k)) y + MN (quo t (two + k)) ≐
      inst2 gN (quo t (two + k)) y + MP (quo t (two + k)) := by
  have apos := two_add_pos (Γ := Γ) k
  have hat : Γ ⊢[PRAAx] le (two + k) t := a_le ht hk
  have u1 : Γ ⊢[PRAAx] le one (quo t (two + k)) :=
    le_quo_of_mul_le apos (le_congr (mul_one_r _).eqSymm (.eqRefl _) hat)
  have h1 : Γ ⊢[PRAAx] le ((two + k) * quo t (two + k)) t := le_of_eq_add (d := rem t (two + k)) (div_eq apos)
  have ult : Γ ⊢[PRAAx] lt (quo t (two + k)) t := lt_of_two h1 (le_add_right two k) u1
  have uX : Γ ⊢[PRAAx] le (quo t (two + k)) X := le_trans (le_trans (le_succ_self _) ult) htX
  have z := (v_at gP gN (quo t (two + k)) X y).eqSymm.eqTrans (sum_zero_elim (vB gP gN) hW ult)
  exact eq_of_viol (bits0 (sg_of_one_le u1) (gle_of_le uX) z)

/-- The term `2 + k` of the four tails. -/
theorem tail_pt (gP gN : PTm 2) {X y t k : PTm n}
    (hW : Γ ⊢[PRAAx] ap2 (sumF (vB gP gN)) t (pairT X y) ≐ zero) (ht : Γ ⊢[PRAAx] t ≐ succ (pred t))
    (htX : Γ ⊢[PRAAx] le t X) (hk : Γ ⊢[PRAAx] lt k (pred t)) :
    Γ ⊢[PRAAx] inst2 (offB (rowB gP)) k (pairT two (pairT t y)) + inst2 (offB GNB) k (pairT two t) ≐
      inst2 (offB (rowB gN)) k (pairT two (pairT t y)) + inst2 (offB GPB) k (pairT two t) := by
  have eP : Γ ⊢[PRAAx] inst2 (offB (rowB gP)) k (pairT two (pairT t y)) ≐
      sg (two + k) * inst2 gP (quo t (two + k)) y := (off_two _ _ _).eqTrans (row_at gP _ _ _)
  have eN : Γ ⊢[PRAAx] inst2 (offB (rowB gN)) k (pairT two (pairT t y)) ≐
      sg (two + k) * inst2 gN (quo t (two + k)) y := (off_two _ _ _).eqTrans (row_at gN _ _ _)
  have eMP : Γ ⊢[PRAAx] inst2 (offB GPB) k (pairT two t) ≐ sg (two + k) * MP (quo t (two + k)) := by
    have h := off_two (Γ := Γ) GPB k t
    rw [inst2_GPB] at h
    exact h
  have eMN : Γ ⊢[PRAAx] inst2 (offB GNB) k (pairT two t) ≐ sg (two + k) * MN (quo t (two + k)) := by
    have h := off_two (Γ := Γ) GNB k t
    rw [inst2_GNB] at h
    exact h
  exact (congrAdd eP eMN).eqTrans ((scale_eq (agree_quo gP gN hW ht htX hk)).eqTrans (congrAdd eN eMP).eqSymm)

/-! ## The step -/

theorem fin_alg {SgP SgN SMP SMN TgP TgN TMP TMN gp gn mp mn s : PTm n}
    (e1 : Γ ⊢[PRAAx] SgP ≐ zero + gp + TgP) (e2 : Γ ⊢[PRAAx] SgN ≐ zero + gn + TgN)
    (e3 : Γ ⊢[PRAAx] SMP ≐ zero + mp + TMP) (e4 : Γ ⊢[PRAAx] SMN ≐ zero + mn + TMN)
    (eR : Γ ⊢[PRAAx] SgP ≐ s + SgN) (eM : Γ ⊢[PRAAx] SMP ≐ s + SMN)
    (eT : Γ ⊢[PRAAx] TgP + TMN ≐ TgN + TMP) : Γ ⊢[PRAAx] gp + mn ≐ gn + mp := by
  ipra_lc -natEq e1 - natEq e4 + natEq e2 + natEq e3 + natEq eR - natEq eM - natEq eT

theorem row_zero (g : PTm 2) (s y : PTm n) : Γ ⊢[PRAAx] inst2 (rowB g) zero (pairT s y) ≐ zero :=
  (row_at g zero s y).eqTrans (zero_mul_l sg_zero _)

theorem row_one (g : PTm 2) (s y : PTm n) : Γ ⊢[PRAAx] inst2 (rowB g) one (pairT s y) ≐ inst2 g s y :=
  (row_at g one s y).eqTrans ((congrMul (sg_succ zero)
    (congrInst2 g (AnalyticNumberTheory.RSA.quo_one s) (.eqRefl _))).eqTrans (one_mul _))

theorem G_zero (t : PTm n) : Γ ⊢[PRAAx] inst2 GPB zero t ≐ zero ⋏ (inst2 GNB zero t ≐ zero) := by
  rw [inst2_GPB, inst2_GNB]
  exact .andI (zero_mul_l sg_zero _) (zero_mul_l sg_zero _)

theorem G_one (t : PTm n) : Γ ⊢[PRAAx] inst2 GPB one t ≐ MP t ⋏ (inst2 GNB one t ≐ MN t) := by
  rw [inst2_GPB, inst2_GNB]
  have q := AnalyticNumberTheory.RSA.quo_one (Γ := Γ) t
  exact .andI
    ((congrMul (sg_succ zero) (congrAp2 (sumF (bS aPB)) q (.eqRefl _))).eqTrans (one_mul _))
    ((congrMul (sg_succ zero) (congrAp2 (sumF (bS aNB)) q (.eqRefl _))).eqTrans (one_mul _))

/-- If the tables agree below `t`, they agree at `t`, for `1 ≤ t ≤ X`. -/
theorem point (gP gN : PTm 2) {X y t : PTm n}
    (hE : Γ ⊢[PRAAx] ap2 (sumF (errB gP gN)) (succ X) y ≐ zero)
    (hW : Γ ⊢[PRAAx] ap2 (sumF (vB gP gN)) t (pairT X y) ≐ zero) (ht : Γ ⊢[PRAAx] t ≐ succ (pred t))
    (htX : Γ ⊢[PRAAx] le t X) : Γ ⊢[PRAAx] inst2 gP t y + MN t ≐ inst2 gN t y + MP t := by
  have ltX : Γ ⊢[PRAAx] lt t (succ X) := (succ_monus_succ _ _).eqTrans htX
  have zE := sum_zero_elim (errB gP gN) hE ltX
  rw [inst2_err] at zE
  have eR : Γ ⊢[PRAAx] Sg gP t y ≐ sg t + Sg gN t y := eq_of_viol zE
  have eM := mertens_floor (Γ := Γ) t
  have e1 : Γ ⊢[PRAAx] Sg gP t y ≐ zero + inst2 gP t y +
      ap2 (sumF (offB (rowB gP))) (pred t) (pairT two (pairT t y)) :=
    (split_two (rowB gP) ht).eqTrans (congrAdd (congrAdd (row_zero gP t y) (row_one gP t y)) (.eqRefl _))
  have e2 : Γ ⊢[PRAAx] Sg gN t y ≐ zero + inst2 gN t y +
      ap2 (sumF (offB (rowB gN))) (pred t) (pairT two (pairT t y)) :=
    (split_two (rowB gN) ht).eqTrans (congrAdd (congrAdd (row_zero gN t y) (row_one gN t y)) (.eqRefl _))
  have e3 : Γ ⊢[PRAAx] ap2 (sumF GPB) (succ t) t ≐ zero + MP t +
      ap2 (sumF (offB GPB)) (pred t) (pairT two t) :=
    (split_two GPB ht).eqTrans (congrAdd (congrAdd (Prf.andE₁ (G_zero t)) (Prf.andE₁ (G_one t))) (.eqRefl _))
  have e4 : Γ ⊢[PRAAx] ap2 (sumF GNB) (succ t) t ≐ zero + MN t +
      ap2 (sumF (offB GNB)) (pred t) (pairT two t) :=
    (split_two GNB ht).eqTrans (congrAdd (congrAdd (Prf.andE₂ (G_zero t)) (Prf.andE₂ (G_one t))) (.eqRefl _))
  have eT : Γ ⊢[PRAAx] ap2 (sumF (offB (rowB gP))) (pred t) (pairT two (pairT t y)) +
        ap2 (sumF (offB GNB)) (pred t) (pairT two t) ≐
      ap2 (sumF (offB (rowB gN))) (pred t) (pairT two (pairT t y)) +
        ap2 (sumF (offB GPB)) (pred t) (pairT two t) := by
    refine sum_cross (offB (rowB gP)) (offB GNB) (offB (rowB gN)) (offB GPB) (.allI (.impI ?_))
    have hW' : Γ.map Fm.shift ⊢[PRAAx]
        ap2 (sumF (vB gP gN)) (Syn.shift t) (pairT (Syn.shift X) (Syn.shift y)) ≐ zero := by
      simpa [Fm.shift, Syn.shift] using hW.shift
    have ht' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift t ≐ succ (pred (Syn.shift t)) := by
      simpa [Fm.shift, Syn.shift] using ht.shift
    have htX' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift t) (Syn.shift X) := by
      simpa [Fm.shift, Syn.shift] using htX.shift
    have s1 : Syn.shift (pairT two (pairT t y)) = pairT two (pairT (Syn.shift t) (Syn.shift y)) := by
      simp [Syn.shift]
    have s2 : Syn.shift (pairT two t) = pairT two (Syn.shift t) := by simp [Syn.shift]
    have s3 : Syn.shift (pred t) = pred (Syn.shift t) := by simp [Syn.shift]
    rw [s1, s2, s3]
    exact tail_pt gP gN hW'.wk ht'.wk htX'.wk Prf.hyp0
  exact fin_alg e1 e2 e3 e4 eR eM eT

/-- The disagreement at `t` vanishes when all disagreements below `t` do. -/
theorem v_step (gP gN : PTm 2) {X y t : PTm n}
    (hE : Γ ⊢[PRAAx] ap2 (sumF (errB gP gN)) (succ X) y ≐ zero)
    (hW : Γ ⊢[PRAAx] ap2 (sumF (vB gP gN)) t (pairT X y) ≐ zero) :
    Γ ⊢[PRAAx] inst2 (vB gP gN) t (pairT X y) ≐ zero := by
  refine (v_at gP gN t X y).eqTrans ?_
  refine .orE (zero_or_succ t) ?_ ?_
  · exact zero_mul_l ((congrSg Prf.hyp0).eqTrans sg_zero) _
  · refine .orE (lt_or_le X t) ?_ ?_
    · have g0 : (lt X t :: (t ≐ succ (pred t)) :: Γ) ⊢[PRAAx] gle t X ≐ zero := gle_above Prf.hyp0
      exact (congrMul (.eqRefl _) (zero_mul_l g0 _)).eqTrans (mul_zero _)
    · have p := point gP gN hE.wk.wk hW.wk.wk
        (Prf.hyp1 : (le t X :: (t ≐ succ (pred t)) :: Γ) ⊢[PRAAx] t ≐ succ (pred t)) Prf.hyp0
      exact (congrMul (.eqRefl _) ((congrMul (.eqRefl _) (viol_of_eq p)).eqTrans (mul_zero _))).eqTrans
        (mul_zero _)

/-! ## The induction -/

/-- No disagreement below `t`, for every `t`. -/
theorem W_zero (gP gN : PTm 2) {X y : PTm n}
    (hE : Γ ⊢[PRAAx] ap2 (sumF (errB gP gN)) (succ X) y ≐ zero) (t : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (vB gP gN)) t (pairT X y) ≐ zero := by
  have sY : Syn.shift (pairT X y) = pairT (Syn.shift X) (Syn.shift y) := by simp [Syn.shift]
  have hE' : Γ.map Fm.shift ⊢[PRAAx]
      ap2 (sumF (errB gP gN)) (succ (Syn.shift X)) (Syn.shift y) ≐ zero := by
    simpa [Fm.shift, Syn.shift] using hE.shift
  have hall : Γ ⊢[PRAAx] Fm.all (ap2 (sumF (vB gP gN)) (var 0) (pairT (Syn.shift X) (Syn.shift y)) ≐ zero) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact sum_zero _ _
    · simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact (sum_succ' _ _ _).eqTrans ((congrAdd Prf.hyp0 (v_step gP gN hE'.wk Prf.hyp0)).eqTrans (add_zero _))
  have h2 := Prf.allE t hall
  simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h2
  exact h2

/-- **`thm:floor-recurrence`, uniqueness**: a table `g = g⁺ − g⁻` that satisfies the floor recurrence for all
`s ≤ X` agrees with the Mertens function on `1 ≤ t ≤ X`: `g⁺(t) + M⁻(t) = g⁻(t) + M⁺(t)`. -/
theorem mertens_unique (gP gN : PTm 2) {X y t : PTm n}
    (hE : Γ ⊢[PRAAx] ap2 (sumF (errB gP gN)) (succ X) y ≐ zero) (ht : Γ ⊢[PRAAx] t ≐ succ (pred t))
    (htX : Γ ⊢[PRAAx] le t X) : Γ ⊢[PRAAx] inst2 gP t y + MN t ≐ inst2 gN t y + MP t :=
  point gP gN hE (W_zero gP gN hE t) ht htX

/-! ## The Mertens function satisfies the hypothesis -/

theorem Sg_mP (s y : PTm n) : Γ ⊢[PRAAx] Sg mPB s y ≐ ap2 (sumF GPB) (succ s) s := by
  refine sum_congr_bounded (rowB mPB) GPB (pairT s y) s (succ s) (.allI (.impI ?_))
  rw [shift_pairT, inst2_GPB]
  have h := row_at (Γ := lt (var 0) (Syn.shift (succ s)) :: Γ.map Fm.shift) mPB (var 0) (Syn.shift s)
    (Syn.shift y)
  rw [inst2_mP] at h
  exact h

theorem Sg_mN (s y : PTm n) : Γ ⊢[PRAAx] Sg mNB s y ≐ ap2 (sumF GNB) (succ s) s := by
  refine sum_congr_bounded (rowB mNB) GNB (pairT s y) s (succ s) (.allI (.impI ?_))
  rw [shift_pairT, inst2_GNB]
  have h := row_at (Γ := lt (var 0) (Syn.shift (succ s)) :: Γ.map Fm.shift) mNB (var 0) (Syn.shift s)
    (Syn.shift y)
  rw [inst2_mN] at h
  exact h

/-- The Mertens function satisfies the floor recurrence at every `s ≤ X`. -/
theorem mertens_err (X y : PTm n) : Γ ⊢[PRAAx] ap2 (sumF (errB mPB mNB)) (succ X) y ≐ zero := by
  refine sum_zero_of_bounded (errB mPB mNB) y (succ X) (.allI (.impI ?_))
  rw [inst2_err]
  exact viol_of_eq ((Sg_mP _ _).eqTrans ((mertens_floor _).eqTrans (congrAdd (.eqRefl _) (Sg_mN _ _).eqSymm)))

end LeanProofs.IPRA.AnalyticNumberTheory.MertensUnique
