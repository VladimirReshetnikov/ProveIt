import IPRADerivations.Foundations.ProductSumDomination
import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Combinatorics.BellLeastPeriod
import IPRADerivations.Combinatorics.CatalanPowers

/-!
# A finite coefficient inequality: log-concavity from a convolution recurrence

Packet: `combinatorics/bell_numbers_ipra`, `lem:coefficient-logconcave`:

"Let `x_0 = 1, x_1, x_2, …` be nonnegative rational numbers such that
`x_j x_{k−1} ≥ x_{j−1} x_k` (`1 ≤ j < k`). Let `a_0 = 1`, put `a_t = 0` for `t < 0`, and define
`r a_r = Σ_{j=1}^{r} x_j a_{r−j}` (`r ≥ 1`). Then, for `1 ≤ m ≤ n`,
`a_m a_n ≥ a_{m−1} a_{n+1}`. Only `x_0, …, x_{n+1}` and `a_0, …, a_{n+1}` occur in each
assertion."

The proof clears denominators ("Clearing the product of denominators makes the invariant an
integer inequality test on a finite table"). Here the sequences are natural-number valued
bodies `X(j, y)`, `A(r, y)` with a parameter `y`, scaled by the common factor `x_0 = X(0, y)`:
the hypotheses (`Hyp`) are, for a bound `N = bd y`,

* `pos`: `x_0 ≥ 1`;
* `recur`: `x_0 (r + 1) a_{r+1} = Σ_{i ≤ r} x_{i+1} a_{r−i}` for `r < N`;
* `xlc`: `x_j x_{k+1} ≤ x_{j+1} x_k` for `j < k < N`.

They are derivations valid in every context and for all terms, so they can be used under the
binders of the inductions. With rational `x_j = X_j / x_0` and `a_r = A_r / x_0` (and `x_0`
their common denominator) these are the hypotheses of the lemma; every inequality of the proof
is homogeneous, so the scale occurs only in `recur`.

The conclusion, with `m = μ + 1` and `n = μ + δ + 1`:
`a_μ a_{μ+δ+2} ≤ a_{μ+1} a_{μ+δ+1}` whenever `μ + δ + 2 ≤ N` (`coefficient_logconcave`).

The steps:

* `recB`, `idB`, `id2`: the second recurrence `x_0 (r + 1) a_r = Σ_{i ≤ r} x_i a_{r−i}` ("The
  recurrence, with its `x_0 a_r` term restored");
* `iB`, `oB`, `lc_elim`: the bit of the statement for all `μ < M` and all admissible `δ`
  (`Foundations/BoundedReflection.allB`, nested); this is the induction formula ("retain the
  Boolean conjunction of these inequalities ... reached so far");
* `spread`: `a_c a_D ≤ a_{c+t} a_{D−t}` for `c + 2t ≤ D`, by `t` unit moves, each an instance
  of the bit at a smaller first index; `core_le`, `ab_le`: `α_k β_j ≤ α_j β_k` for `j < k`,
  where `α_j = [j ≤ M] a_{M−j}` and `β_j = a_{m−j}` (the two cases `A ≤ E` and `E ≤ A` of the
  packet's proof);
* `pB`, `qB`, `rB`, `sB`: the families `x_{j+1} α_j`, `x_j β_j`, `x_j α_j`, `x_{j+1} β_j`;
  `pair_alg`, `pair_le`, `diag_le`: the pair and diagonal conditions,
  `(x_{j+1} x_k − x_j x_{k+1})(α_j β_k − α_k β_j) ≥ 0` (the summand of `eq:paired-logconcavity`);
* `dom_all`: `(Σ r)(Σ s) ≤ (Σ p)(Σ q)` by `Foundations/ProductSumDomination.dom_step`, so the
  double sum of `eq:paired-logconcavity` is never formed;
* `sum_P`, `sum_Q`, `sum_R`, `sum_S`: the four sums are `x_0 (M + 1) a_{M+1}`, `x_0 (m + 1) a_m`,
  `x_0 (M + 1) a_M`, `x_0 (m + 1) a_{m+1}` (`sum_trunc` for the convention `a_t = 0`, `t < 0`);
* `lc_main`: the inequality at `(M, D)` after cancelling `x_0² (M + 1)(m + 1)`;
  `o_one`, `lc_all`: the induction on `M`.

`Combinatorics/BellLogConcave` instantiates the hypotheses for the Bell numbers.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CoefficientLogConcave

open_ipra
open LeanProofs.IPRA.Combinatorics.Stirling (gle gle_of_le gle_above)
open LeanProofs.IPRA.Combinatorics.BellTouchardPower (pair_congr succ_monus_of_le le_of_lt_succ)
open LeanProofs.IPRA.Combinatorics.BellLeastPeriod (allB_extend ne_of_one)
open LeanProofs.IPRA.Combinatorics.CatalanPowers (shift_pair shift_succ shift_zero monus_le_left
  lt_succ_of_le)
open LeanProofs.IPRA.Foundations.BoundedReflection (allB allB_zero all_elim all_intro all_cases
  zero_of_compl_ne one_ne_zero sgB)
open LeanProofs.IPRA.Foundations.ProductSumDomination (sum_trunc dom_step)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Bodies by substitution -/

/-- `f(a(i, w), b(i, w))` as a body. -/
def sub2 (f a b : PTm 2) : PTm 2 := Syn.subst ![a, b] f

theorem inst2_sub2 (f a b : PTm 2) (i w : PTm n) :
    inst2 (sub2 f a b) i w = inst2 f (inst2 a i w) (inst2 b i w) := by
  simp only [inst2, sub2, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

theorem inst2_mul (a b : PTm 2) (i w : PTm n) :
    inst2 (a * b) i w = inst2 a i w * inst2 b i w := by simp [inst2]

theorem inst2_monus (a b : PTm 2) (i w : PTm n) :
    inst2 (monus a b) i w = monus (inst2 a i w) (inst2 b i w) := by simp [inst2]

theorem inst2_ap2 (f : PR 2) (a b : PTm 2) (i w : PTm n) :
    inst2 (ap2 f a b) i w = ap2 f (inst2 a i w) (inst2 b i w) := by simp [inst2]

section General

variable (X A : PTm 2) (Nb : PTm 1)

/-- The bound `N` of the parameter `y`. -/
abbrev bd (y : PTm n) : PTm n := Syn.subst ![y] Nb

/-- `x_{i+1} a_{r−i}`, over `0 = i`, `1 = ⟨r, y⟩`. -/
def recB : PTm 2 :=
  sub2 X (succ (var 0)) (sndT (var 1)) * sub2 A (monus (fstT (var 1)) (var 0)) (sndT (var 1))

theorem rec_at (i r y : PTm n) :
    Γ ⊢[PRAAx] inst2 (recB X A) i (pairT r y) ≐ inst2 X (succ i) y * inst2 A (monus r i) y := by
  have h : inst2 (recB X A) i (pairT r y) = inst2 X (succ i) (sndT (pairT r y)) *
      inst2 A (monus (fstT (pairT r y)) i) (sndT (pairT r y)) := by
    simp only [recB, inst2_mul, inst2_sub2]; simp [inst2]
  rw [h]
  exact congrMul (congrInst2 X (.eqRefl _) (snd_pair _ _))
    (congrInst2 A (congrMonus (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))

/-- `x_i a_{r−i}`, over `0 = i`, `1 = ⟨r, y⟩`. -/
def idB : PTm 2 :=
  sub2 X (var 0) (sndT (var 1)) * sub2 A (monus (fstT (var 1)) (var 0)) (sndT (var 1))

theorem id_at (i r y : PTm n) :
    Γ ⊢[PRAAx] inst2 (idB X A) i (pairT r y) ≐ inst2 X i y * inst2 A (monus r i) y := by
  have h : inst2 (idB X A) i (pairT r y) = inst2 X i (sndT (pairT r y)) *
      inst2 A (monus (fstT (pairT r y)) i) (sndT (pairT r y)) := by
    simp only [idB, inst2_mul, inst2_sub2]; simp [inst2]
  rw [h]
  exact congrMul (congrInst2 X (.eqRefl _) (snd_pair _ _))
    (congrInst2 A (congrMonus (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))

/-- The hypotheses of `lem:coefficient-logconcave`, scaled by `x_0`: derivations valid in every
context and for all terms. -/
structure Hyp : Prop where
  /-- `x_0 ≥ 1`. -/
  pos : ∀ {n : ℕ} {Γ : List (Fm PTm n)} (y : PTm n), Γ ⊢[PRAAx] lt zero (inst2 X zero y)
  /-- `x_0 (r + 1) a_{r+1} = Σ_{i ≤ r} x_{i+1} a_{r−i}` for `r < N`. -/
  recur : ∀ {n : ℕ} {Γ : List (Fm PTm n)} (r y : PTm n), (Γ ⊢[PRAAx] lt r (bd Nb y)) →
    (Γ ⊢[PRAAx] inst2 X zero y * (succ r * inst2 A (succ r) y) ≐
      ap2 (sumF (recB X A)) (succ r) (pairT r y))
  /-- `x_j x_{k+1} ≤ x_{j+1} x_k` for `j < k < N`. -/
  xlc : ∀ {n : ℕ} {Γ : List (Fm PTm n)} (j k y : PTm n), (Γ ⊢[PRAAx] lt j k) →
    (Γ ⊢[PRAAx] lt k (bd Nb y)) →
    (Γ ⊢[PRAAx] le (inst2 X j y * inst2 X (succ k) y) (inst2 X (succ j) y * inst2 X k y))

/-! ## The second recurrence -/

theorem id2_zero (y : PTm n) :
    Γ ⊢[PRAAx] inst2 X zero y * (succ zero * inst2 A zero y) ≐
      ap2 (sumF (idB X A)) (succ zero) (pairT zero y) :=
  ((sum_singleton (idB X A) (pairT zero y)).eqTrans
    ((id_at X A zero zero y).eqTrans
      (congrMul (.eqRefl _)
        ((congrInst2 A (monus_zero zero) (.eqRefl _)).eqTrans (one_mul _).eqSymm)))).eqSymm

variable {X A Nb}

theorem id2_succ (hyp : Hyp X A Nb) {r y : PTm n} (h : Γ ⊢[PRAAx] lt r (bd Nb y)) :
    Γ ⊢[PRAAx] inst2 X zero y * (succ (succ r) * inst2 A (succ r) y) ≐
      ap2 (sumF (idB X A)) (succ (succ r)) (pairT (succ r) y) := by
  have f₀ := natEq ((id_at (Γ := Γ) X A zero (succ r) y).eqTrans
    (congrMul (.eqRefl _) (congrInst2 A (monus_zero (succ r)) (.eqRefl _))))
  have tail : Γ ⊢[PRAAx] ap2 (sumF (shiftBody (idB X A))) (succ r) (pairT (succ r) y) ≐
      ap2 (sumF (recB X A)) (succ r) (pairT r y) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_shiftBody]
    simp only [shift_pair, shift_succ]
    exact (id_at X A _ _ _).eqTrans ((congrMul (.eqRefl _)
      (congrInst2 A (succ_monus_succ _ _) (.eqRefl _))).eqTrans (rec_at X A _ _ _).eqSymm)
  ipra_lc natEq (hyp.recur (Γ := Γ) r y h) - natEq (sum_shift (Γ := Γ) (idB X A) (succ r) (pairT (succ r) y)) - f₀ -
    natEq tail

theorem id2_congr {r r' y : PTm n} (e : Γ ⊢[PRAAx] r ≐ r')
    (h : Γ ⊢[PRAAx] inst2 X zero y * (succ r' * inst2 A r' y) ≐
      ap2 (sumF (idB X A)) (succ r') (pairT r' y)) :
    Γ ⊢[PRAAx] inst2 X zero y * (succ r * inst2 A r y) ≐
      ap2 (sumF (idB X A)) (succ r) (pairT r y) :=
  (congrMul (.eqRefl _) (congrMul (congrSucc e) (congrInst2 A e (.eqRefl _)))).eqTrans
    (h.eqTrans (congrAp2 _ (congrSucc e.eqSymm) (pair_congr e.eqSymm (.eqRefl _))))

/-- `x_0 (r + 1) a_r = Σ_{i ≤ r} x_i a_{r−i}` for `r ≤ N`. -/
theorem id2 (hyp : Hyp X A Nb) {r y : PTm n} (h : Γ ⊢[PRAAx] le r (bd Nb y)) :
    Γ ⊢[PRAAx] inst2 X zero y * (succ r * inst2 A r y) ≐
      ap2 (sumF (idB X A)) (succ r) (pairT r y) := by
  refine .orE (zero_or_succ r) ?_ ?_
  · exact id2_congr Prf.hyp0 (id2_zero X A y)
  · exact id2_congr Prf.hyp0 (id2_succ hyp
      (le_congr (Prf.hyp0 (Γ := Γ) (φ := r ≐ succ (pred r))) (.eqRefl _) h.wk))

variable (A Nb)

/-! ## The statement as a bit -/

/-- The bound as a body over `1 = y`. -/
def bdB : PTm 2 := Syn.subst ![var 1] Nb

theorem inst2_bdB (i y : PTm n) : inst2 (bdB Nb) i y = bd Nb y := by
  simp only [inst2, bdB, Syn.subst_subst]
  congr 1; funext j; fin_cases j; simp

/-- The bit `[a_μ a_{μ+δ+2} ≤ a_{μ+1} a_{μ+δ+1}]`, over `0 = δ`, `1 = ⟨μ, y⟩`. -/
def iB : PTm 2 :=
  monus one (monus
    (sub2 A (fstT (var 1)) (sndT (var 1)) *
      sub2 A (succ (succ (fstT (var 1) + var 0))) (sndT (var 1)))
    (sub2 A (succ (fstT (var 1))) (sndT (var 1)) *
      sub2 A (succ (fstT (var 1) + var 0)) (sndT (var 1))))

theorem i_at (δ μ y : PTm n) :
    Γ ⊢[PRAAx] inst2 (iB A) δ (pairT μ y) ≐
      gle (inst2 A μ y * inst2 A (succ (succ (μ + δ))) y)
        (inst2 A (succ μ) y * inst2 A (succ (μ + δ)) y) := by
  have h : inst2 (iB A) δ (pairT μ y) = monus one (monus
      (inst2 A (fstT (pairT μ y)) (sndT (pairT μ y)) *
        inst2 A (succ (succ (fstT (pairT μ y) + δ))) (sndT (pairT μ y)))
      (inst2 A (succ (fstT (pairT μ y))) (sndT (pairT μ y)) *
        inst2 A (succ (fstT (pairT μ y) + δ)) (sndT (pairT μ y)))) := by
    simp only [iB, inst2_monus, inst2_mul, inst2_sub2]; simp [inst2]
  rw [h]
  have f : Γ ⊢[PRAAx] fstT (pairT μ y) ≐ μ := fst_pair _ _
  have s : Γ ⊢[PRAAx] sndT (pairT μ y) ≐ y := snd_pair _ _
  exact congrMonus (.eqRefl _) (congrMonus
    (congrMul (congrInst2 A f s)
      (congrInst2 A (congrSucc (congrSucc (congrAdd f (.eqRefl _)))) s))
    (congrMul (congrInst2 A (congrSucc f) s)
      (congrInst2 A (congrSucc (congrAdd f (.eqRefl _))) s)))

/-- The bit of the statement at `μ` for all `δ` with `μ + δ + 2 ≤ N`, over `0 = μ`, `1 = y`. -/
def oB : PTm 2 :=
  ap2 (prodF (sgB (iB A))) (monus (bdB Nb) (succ (var 0))) (pairT (var 0) (var 1))

theorem inst2_oB (μ y : PTm n) :
    inst2 (oB A Nb) μ y = allB (iB A) (monus (bd Nb y) (succ μ)) (pairT μ y) := by
  simp only [oB, inst2_ap2, inst2_monus, inst2_bdB]; simp [inst2]

theorem delta_lt {μ δ N : PTm n} (hδ : Γ ⊢[PRAAx] lt (succ (μ + δ)) N) :
    Γ ⊢[PRAAx] lt δ (monus N (succ μ)) := by
  have e' : Γ ⊢[PRAAx] N ≐ (succ δ + monus N (succ (succ (μ + δ)))) + succ μ := by
    ipra_lc natEq (eq_add_of_le hδ)
  exact le_of_eq_add (d := monus N (succ (succ (μ + δ))))
    ((congrMonus e' (.eqRefl _)).eqTrans (add_monus _ _))

/-- The statement at `(μ, δ)` from the bit for all `μ < M`. -/
theorem lc_elim {M μ δ y : PTm n} (hQ : Γ ⊢[PRAAx] allB (oB A Nb) M y ≐ one)
    (hμ : Γ ⊢[PRAAx] lt μ M) (hδ : Γ ⊢[PRAAx] lt (succ (μ + δ)) (bd Nb y)) :
    Γ ⊢[PRAAx] le (inst2 A μ y * inst2 A (succ (succ (μ + δ))) y)
      (inst2 A (succ μ) y * inst2 A (succ (μ + δ)) y) := by
  have a := all_elim (oB A Nb) hQ hμ
  rw [inst2_oB] at a
  have o : Γ ⊢[PRAAx] allB (iB A) (monus (bd Nb y) (succ μ)) (pairT μ y) ≐ one :=
    .orE (all_cases (iB A) _ _) (.botE _ (.impE a.wk Prf.hyp0)) Prf.hyp0
  have b := all_elim (iB A) o (delta_lt hδ)
  have z : Γ ⊢[PRAAx] monus (inst2 A μ y * inst2 A (succ (succ (μ + δ))) y)
      (inst2 A (succ μ) y * inst2 A (succ (μ + δ)) y) ≐ zero :=
    zero_of_compl_ne (.impI (.impE b.wk ((i_at A δ μ y).eqTrans Prf.hyp0)))
  exact z

/-! ## Spreading two indices apart

"Starting with the pair `(min(A, E), max(A, E))`, move one unit at a time from its smaller index
to its larger one until the pair becomes `(C, D)`. At each step the smaller index is less than
`m`, so the induction hypothesis says the product of the two `a`'s cannot increase." -/

theorem shift_bd (y : PTm n) : Syn.shift (bd Nb y) = bd Nb (Syn.shift y) := by
  simp only [bd, Syn.shift, Syn.subst_subst]
  congr 1; funext j; fin_cases j; simp

variable {A Nb}

theorem spread_step_aux {M c D t δ y : PTm n} (hQ : Γ ⊢[PRAAx] allB (oB A Nb) M y ≐ one)
    (hD : Γ ⊢[PRAAx] le D (bd Nb y))
    (ih : Γ ⊢[PRAAx] le (inst2 A c y * inst2 A D y) (inst2 A (c + t) y * inst2 A (monus D t) y))
    (h1 : Γ ⊢[PRAAx] le (c + succ t) M) (eD : Γ ⊢[PRAAx] D ≐ (c + succ t + succ t) + δ) :
    Γ ⊢[PRAAx] le (inst2 A c y * inst2 A D y)
      (inst2 A (c + succ t) y * inst2 A (monus D (succ t)) y) := by
  have d1 : Γ ⊢[PRAAx] D ≐ succ (succ ((c + t) + δ)) + t := by
    ipra_lc natEq eD
  have d2 : Γ ⊢[PRAAx] D ≐ succ ((c + t) + δ) + succ t := by
    ipra_lc natEq eD
  have i1 : Γ ⊢[PRAAx] monus D t ≐ succ (succ ((c + t) + δ)) :=
    (congrMonus d1 (.eqRefl _)).eqTrans (add_monus _ _)
  have i2 : Γ ⊢[PRAAx] monus D (succ t) ≐ succ ((c + t) + δ) :=
    (congrMonus d2 (.eqRefl _)).eqTrans (add_monus _ _)
  have hμ : Γ ⊢[PRAAx] lt (c + t) M := le_congr (add_succ c t) (.eqRefl _) h1
  have hδ : Γ ⊢[PRAAx] lt (succ ((c + t) + δ)) (bd Nb y) :=
    le_trans (le_of_eq_add (d := t) d1) hD
  have lc := lc_elim A Nb hQ hμ hδ
  have lc' := le_congr (congrMul (.eqRefl _) (congrInst2 A i1.eqSymm (.eqRefl _)))
    (congrMul (congrInst2 A (add_succ c t).eqSymm (.eqRefl _))
      (congrInst2 A i2.eqSymm (.eqRefl _))) lc
  exact le_trans ih lc'

variable (A)

/-- The induction formula of `spread`; variable `0 = t`. -/
abbrev spF (M c D y : PTm n) : Fm PTm (n + 1) :=
  le (Syn.shift c + var 0) (Syn.shift M) ⟶ (le (Syn.shift c + var 0 + var 0) (Syn.shift D) ⟶
    le (inst2 A (Syn.shift c) (Syn.shift y) * inst2 A (Syn.shift D) (Syn.shift y))
      (inst2 A (Syn.shift c + var 0) (Syn.shift y) *
        inst2 A (monus (Syn.shift D) (var 0)) (Syn.shift y)))

variable {A}

/-- `a_c a_D ≤ a_{c+t} a_{D−t}` for `c + 2t ≤ D ≤ N`, given the statement for all `μ < M` and
`c + t ≤ M`. -/
theorem spread {M c D y : PTm n} (hQ : Γ ⊢[PRAAx] allB (oB A Nb) M y ≐ one)
    (hD : Γ ⊢[PRAAx] le D (bd Nb y)) (t : PTm n) (h1 : Γ ⊢[PRAAx] le (c + t) M)
    (h2 : Γ ⊢[PRAAx] le (c + t + t) D) :
    Γ ⊢[PRAAx] le (inst2 A c y * inst2 A D y) (inst2 A (c + t) y * inst2 A (monus D t) y) := by
  have hall : Γ ⊢[PRAAx] Fm.all (spF A M c D y) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _, le_QF _ _⟩ ?_ ?_
    · have b : Γ ⊢[PRAAx] le (c + zero) M ⟶ (le (c + zero + zero) D ⟶
          le (inst2 A c y * inst2 A D y) (inst2 A (c + zero) y * inst2 A (monus D zero) y)) :=
        .impI (.impI (le_congr (.eqRefl _) (congrMul (congrInst2 A (add_zero c).eqSymm (.eqRefl _))
          (congrInst2 A (monus_zero D).eqSymm (.eqRefl _))) (le_refl _)))
      simpa [subst_inst2] using b
    · have hQ' : (Γ.map Fm.shift) ⊢[PRAAx]
          allB (oB A Nb) (Syn.shift M) (Syn.shift y) ≐ one := by
        simpa [Fm.shift, Syn.shift] using hQ.shift
      have hD' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift D) (Syn.shift (bd Nb y)) := by
        simpa [Fm.shift, Syn.shift] using hD.shift
      rw [shift_bd] at hD'
      have st : (spF A M c D y :: Γ.map Fm.shift) ⊢[PRAAx]
          le (Syn.shift c + succ (var 0)) (Syn.shift M) ⟶
            (le (Syn.shift c + succ (var 0) + succ (var 0)) (Syn.shift D) ⟶
              le (inst2 A (Syn.shift c) (Syn.shift y) * inst2 A (Syn.shift D) (Syn.shift y))
                (inst2 A (Syn.shift c + succ (var 0)) (Syn.shift y) *
                  inst2 A (monus (Syn.shift D) (succ (var 0))) (Syn.shift y))) := by
        refine .impI (.impI ?_)
        have g2 : (le (Syn.shift c + succ (var 0) + succ (var 0)) (Syn.shift D) ::
            le (Syn.shift c + succ (var 0)) (Syn.shift M) :: spF A M c D y :: Γ.map Fm.shift)
            ⊢[PRAAx] le (Syn.shift c + succ (var 0) + succ (var 0)) (Syn.shift D) := Prf.hyp0
        have g1 : (le (Syn.shift c + succ (var 0) + succ (var 0)) (Syn.shift D) ::
            le (Syn.shift c + succ (var 0)) (Syn.shift M) :: spF A M c D y :: Γ.map Fm.shift)
            ⊢[PRAAx] le (Syn.shift c + succ (var 0)) (Syn.shift M) := .hyp (by simp)
        have gF : (le (Syn.shift c + succ (var 0) + succ (var 0)) (Syn.shift D) ::
            le (Syn.shift c + succ (var 0)) (Syn.shift M) :: spF A M c D y :: Γ.map Fm.shift)
            ⊢[PRAAx] spF A M c D y := .hyp (by simp)
        have a1 : (le (Syn.shift c + succ (var 0) + succ (var 0)) (Syn.shift D) ::
            le (Syn.shift c + succ (var 0)) (Syn.shift M) :: spF A M c D y :: Γ.map Fm.shift)
            ⊢[PRAAx] le (Syn.shift c + var 0) (Syn.shift M) :=
          le_trans (le_of_eq_add (d := one) (by ipra_ring)) g1
        have a2 : (le (Syn.shift c + succ (var 0) + succ (var 0)) (Syn.shift D) ::
            le (Syn.shift c + succ (var 0)) (Syn.shift M) :: spF A M c D y :: Γ.map Fm.shift)
            ⊢[PRAAx] le (Syn.shift c + var 0 + var 0) (Syn.shift D) :=
          le_trans (le_of_eq_add (d := two) (by ipra_ring)) g2
        have ih := Prf.impE (Prf.impE gF a1) a2
        exact spread_step_aux hQ'.wk.wk.wk hD'.wk.wk.wk ih g1 (eq_add_of_le g2)
      simpa [subst_repl_shift, Syn.repl_zero, subst_inst2] using st
  have h3 := Prf.allE t hall
  have h4 : Γ ⊢[PRAAx] le (c + t) M ⟶ (le (c + t + t) D ⟶
      le (inst2 A c y * inst2 A D y) (inst2 A (c + t) y * inst2 A (monus D t) y)) := by
    simpa [Syn.subst_inst_shift, Syn.inst_zero, subst_inst2] using h3
  exact .impE (.impE h4 h1) h2

/-- `a_{M−k} a_{m−j} ≤ a_{M−j} a_{m−k}` for `j < k ≤ M`, `m = M + D + 1 ≤ N`. -/
theorem core_le {j k M D y : PTm n} (hQ : Γ ⊢[PRAAx] allB (oB A Nb) M y ≐ one)
    (hjk : Γ ⊢[PRAAx] lt j k) (hkM : Γ ⊢[PRAAx] le k M)
    (hm : Γ ⊢[PRAAx] le (succ (M + D)) (bd Nb y)) :
    Γ ⊢[PRAAx] le (inst2 A (monus M k) y * inst2 A (monus (succ (M + D)) j) y)
      (inst2 A (monus M j) y * inst2 A (monus (succ (M + D)) k) y) := by
  have eM := natEq (eq_add_of_le hkM)      -- `M = k + (M ∸ k)`
  have ek := natEq (eq_add_of_le hjk)      -- `k = (j + 1) + (k ∸ (j + 1))`
  have iMj : Γ ⊢[PRAAx] monus M j ≐ monus M k + succ (monus k (succ j)) := by
    refine (congrMonus (b := j + (monus M k + succ (monus k (succ j)))) ?_ (.eqRefl _)).eqTrans
      (add_monus' _ _)
    ipra_lc eM + ek
  have imk : Γ ⊢[PRAAx] monus (succ (M + D)) k ≐ monus M k + succ D := by
    refine (congrMonus (b := k + (monus M k + succ D)) ?_ (.eqRefl _)).eqTrans (add_monus' _ _)
    ipra_lc eM
  have imj : Γ ⊢[PRAAx] monus (succ (M + D)) j ≐
      (monus M k + succ (monus k (succ j))) + succ D := by
    refine (congrMonus (b := j + ((monus M k + succ (monus k (succ j))) + succ D)) ?_
      (.eqRefl _)).eqTrans (add_monus' _ _)
    ipra_lc eM + ek
  have hD : Γ ⊢[PRAAx] le (monus (succ (M + D)) j) (bd Nb y) := le_trans (monus_le_left _ _) hm
  have hcM : Γ ⊢[PRAAx] le (monus M k + succ (monus k (succ j))) M :=
    le_of_eq_add (d := j) (by apply deriveNat; ipra_simps; linear_combination eM + ek)
  refine .orE (le_total (succ (monus k (succ j))) (succ D)) ?_ ?_
  · -- `A ≤ E`: move `t₀ = k − j` units
    have w := natEq (eq_add_of_le (Prf.hyp0 (Γ := Γ)
      (φ := le (succ (monus k (succ j))) (succ D))))
    have h2 : (le (succ (monus k (succ j))) (succ D) :: Γ) ⊢[PRAAx]
        le (monus M k + succ (monus k (succ j)) + succ (monus k (succ j)))
          (monus (succ (M + D)) j) := by
      refine le_congr (.eqRefl _) imj.wk.eqSymm (le_of_eq_add
        (d := monus (succ D) (succ (monus k (succ j)))) ?_)
      ipra_lc w
    have sp := spread hQ.wk hD.wk (succ (monus k (succ j))) hcM.wk h2
    have i4 : (le (succ (monus k (succ j))) (succ D) :: Γ) ⊢[PRAAx]
        monus (monus (succ (M + D)) j) (succ (monus k (succ j))) ≐ monus (succ (M + D)) k := by
      refine (congrMonus (b := (monus M k + succ D) + succ (monus k (succ j))) ?_
        (.eqRefl _)).eqTrans ((add_monus _ _).eqTrans imk.wk.eqSymm)
      refine imj.wk.eqTrans ?_
      ipra_ring
    exact le_congr (.eqRefl _) (congrMul (congrInst2 A iMj.wk.eqSymm (.eqRefl _))
      (congrInst2 A i4 (.eqRefl _))) sp
  · -- `E ≤ A`: move `E − C = D + 1` units
    have w := natEq (eq_add_of_le (Prf.hyp0 (Γ := Γ)
      (φ := le (succ D) (succ (monus k (succ j))))))
    have h1 : (le (succ D) (succ (monus k (succ j))) :: Γ) ⊢[PRAAx] le (monus M k + succ D) M :=
      le_trans (le_of_eq_add (d := monus (succ (monus k (succ j))) (succ D))
        (by apply deriveNat; ipra_simps; linear_combination w)) hcM.wk
    have h2 : (le (succ D) (succ (monus k (succ j))) :: Γ) ⊢[PRAAx]
        le (monus M k + succ D + succ D) (monus (succ (M + D)) j) := by
      refine le_congr (.eqRefl _) imj.wk.eqSymm (le_of_eq_add
        (d := monus (succ (monus k (succ j))) (succ D)) ?_)
      ipra_lc w
    have sp := spread hQ.wk hD.wk (succ D) h1 h2
    have i4 : (le (succ D) (succ (monus k (succ j))) :: Γ) ⊢[PRAAx]
        monus (monus (succ (M + D)) j) (succ D) ≐ monus M j :=
      (congrMonus imj.wk (.eqRefl _)).eqTrans ((add_monus _ _).eqTrans iMj.wk.eqSymm)
    exact le_congr (.eqRefl _) ((congrMul (congrInst2 A imk.wk.eqSymm (.eqRefl _))
      (congrInst2 A i4 (.eqRefl _))).eqTrans (mul_comm _ _)) sp

/-- `α_k β_j ≤ α_j β_k` for `j < k`, with `α_j = [j ≤ M] a_{M−j}` and `β_j = a_{m−j}`. -/
theorem ab_le {j k M D y : PTm n} (hQ : Γ ⊢[PRAAx] allB (oB A Nb) M y ≐ one)
    (hjk : Γ ⊢[PRAAx] lt j k) (hm : Γ ⊢[PRAAx] le (succ (M + D)) (bd Nb y)) :
    Γ ⊢[PRAAx] le ((gle k M * inst2 A (monus M k) y) * inst2 A (monus (succ (M + D)) j) y)
      ((gle j M * inst2 A (monus M j) y) * inst2 A (monus (succ (M + D)) k) y) := by
  refine .orE (lt_or_le M k) ?_ ?_
  · have z : (lt M k :: Γ) ⊢[PRAAx]
        (gle k M * inst2 A (monus M k) y) * inst2 A (monus (succ (M + D)) j) y ≐ zero :=
      mul_eq_zero_of_left (mul_eq_zero_of_left (gle_above Prf.hyp0))
    exact le_congr z.eqSymm (.eqRefl _) (zero_le _)
  · have hkM : (le k M :: Γ) ⊢[PRAAx] le k M := Prf.hyp0
    have hjM : (le k M :: Γ) ⊢[PRAAx] le j M := le_trans (le_trans (le_succ_self j) hjk.wk) hkM
    have c := core_le hQ.wk hjk.wk hkM hm.wk
    exact le_congr
      (congrMul ((congrMul (gle_of_le hkM) (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _)).eqSymm
      (congrMul ((congrMul (gle_of_le hjM) (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _)).eqSymm c

/-! ## The four families -/

variable (X A)

/-- `α_j = [j ≤ M] a_{M−j}`, over `0 = j`, `1 = ⟨M, ⟨m, y⟩⟩`. -/
def alB : PTm 2 :=
  monus one (monus (var 0) (fstT (var 1))) *
    sub2 A (monus (fstT (var 1)) (var 0)) (sndT (sndT (var 1)))
/-- `β_j = a_{m−j}`. -/
def beB : PTm 2 := sub2 A (monus (fstT (sndT (var 1))) (var 0)) (sndT (sndT (var 1)))
/-- `x_j`. -/
def x0B : PTm 2 := sub2 X (var 0) (sndT (sndT (var 1)))
/-- `x_{j+1}`. -/
def x1B : PTm 2 := sub2 X (succ (var 0)) (sndT (sndT (var 1)))
/-- `p_j = x_{j+1} α_j`. -/
def pB : PTm 2 := x1B X * alB A
/-- `q_j = x_j β_j`. -/
def qB : PTm 2 := x0B X * beB A
/-- `r_j = x_j α_j`. -/
def rB : PTm 2 := x0B X * alB A
/-- `s_j = x_{j+1} β_j`. -/
def sB : PTm 2 := x1B X * beB A

theorem al_at (j M m y : PTm n) : Γ ⊢[PRAAx] inst2 (alB A) j (pairT M (pairT m y)) ≐
    gle j M * inst2 A (monus M j) y := by
  have h : inst2 (alB A) j (pairT M (pairT m y)) =
      monus one (monus j (fstT (pairT M (pairT m y)))) *
        inst2 A (monus (fstT (pairT M (pairT m y))) j) (sndT (sndT (pairT M (pairT m y)))) := by
    simp only [alB, inst2_mul, inst2_monus, inst2_sub2]; simp [inst2]
  rw [h]
  have f : Γ ⊢[PRAAx] fstT (pairT M (pairT m y)) ≐ M := fst_pair _ _
  have s : Γ ⊢[PRAAx] sndT (sndT (pairT M (pairT m y))) ≐ y :=
    (snd_pair _ _).sndE
  exact congrMul (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) f))
    (congrInst2 A (congrMonus f (.eqRefl _)) s)

theorem be_at (j M m y : PTm n) : Γ ⊢[PRAAx] inst2 (beB A) j (pairT M (pairT m y)) ≐
    inst2 A (monus m j) y := by
  have h : inst2 (beB A) j (pairT M (pairT m y)) =
      inst2 A (monus (fstT (sndT (pairT M (pairT m y)))) j)
        (sndT (sndT (pairT M (pairT m y)))) := by
    simp only [beB, inst2_sub2]; simp [inst2]
  rw [h]
  have s : Γ ⊢[PRAAx] sndT (pairT M (pairT m y)) ≐ pairT m y := snd_pair _ _
  exact congrInst2 A (congrMonus s.fstE (.eqRefl _))
    s.sndE

theorem x0_at (j M m y : PTm n) : Γ ⊢[PRAAx] inst2 (x0B X) j (pairT M (pairT m y)) ≐
    inst2 X j y := by
  have h : inst2 (x0B X) j (pairT M (pairT m y)) =
      inst2 X j (sndT (sndT (pairT M (pairT m y)))) := by
    simp only [x0B, inst2_sub2]; simp [inst2]
  rw [h]
  exact congrInst2 X (.eqRefl _) (snd_pair _ _).sndE

theorem x1_at (j M m y : PTm n) : Γ ⊢[PRAAx] inst2 (x1B X) j (pairT M (pairT m y)) ≐
    inst2 X (succ j) y := by
  have h : inst2 (x1B X) j (pairT M (pairT m y)) =
      inst2 X (succ j) (sndT (sndT (pairT M (pairT m y)))) := by
    simp only [x1B, inst2_sub2]; simp [inst2]
  rw [h]
  exact congrInst2 X (.eqRefl _) (snd_pair _ _).sndE

theorem p_at (j M m y : PTm n) : Γ ⊢[PRAAx] inst2 (pB X A) j (pairT M (pairT m y)) ≐
    inst2 X (succ j) y * (gle j M * inst2 A (monus M j) y) := by
  rw [pB, inst2_mul]; exact congrMul (x1_at X j M m y) (al_at A j M m y)

theorem q_at (j M m y : PTm n) : Γ ⊢[PRAAx] inst2 (qB X A) j (pairT M (pairT m y)) ≐
    inst2 X j y * inst2 A (monus m j) y := by
  rw [qB, inst2_mul]; exact congrMul (x0_at X j M m y) (be_at A j M m y)

theorem r_at (j M m y : PTm n) : Γ ⊢[PRAAx] inst2 (rB X A) j (pairT M (pairT m y)) ≐
    inst2 X j y * (gle j M * inst2 A (monus M j) y) := by
  rw [rB, inst2_mul]; exact congrMul (x0_at X j M m y) (al_at A j M m y)

theorem s_at (j M m y : PTm n) : Γ ⊢[PRAAx] inst2 (sB X A) j (pairT M (pairT m y)) ≐
    inst2 X (succ j) y * inst2 A (monus m j) y := by
  rw [sB, inst2_mul]; exact congrMul (x1_at X j M m y) (be_at A j M m y)

/-! ## The pair condition -/

/-- `(x_{j+1} x_k − x_j x_{k+1})(α_j β_k − α_k β_j) ≥ 0`, expanded. -/
theorem pair_alg {xj xj1 xk xk1 aj ak bj bk : PTm n} (hu : Γ ⊢[PRAAx] le (xj * xk1) (xj1 * xk))
    (hw : Γ ⊢[PRAAx] le (ak * bj) (aj * bk)) :
    Γ ⊢[PRAAx] le (xj * aj * (xk1 * bk) + xk * ak * (xj1 * bj))
      (xj1 * aj * (xk * bk) + xk1 * ak * (xj * bj)) := by
  refine le_of_eq_add (d := monus (xj1 * xk) (xj * xk1) * monus (aj * bk) (ak * bj)) ?_
  ipra_lc (𝔞 aj * 𝔞 bk - 𝔞 ak * 𝔞 bj) * natEq (eq_add_of_le hu) +
    𝔞 (monus (xj1 * xk) (xj * xk1)) * natEq (eq_add_of_le hw)

variable {X A}

/-- The pair condition of `Foundations/ProductSumDomination.dom_step` for `j < k ≤ m`. -/
theorem pair_le (hyp : Hyp X A Nb) {j k M D y : PTm n}
    (hQ : Γ ⊢[PRAAx] allB (oB A Nb) M y ≐ one) (hjk : Γ ⊢[PRAAx] lt j k)
    (hk : Γ ⊢[PRAAx] lt k (bd Nb y)) (hm : Γ ⊢[PRAAx] le (succ (M + D)) (bd Nb y)) :
    Γ ⊢[PRAAx] le
      (inst2 (rB X A) j (pairT M (pairT (succ (M + D)) y)) *
          inst2 (sB X A) k (pairT M (pairT (succ (M + D)) y)) +
        inst2 (rB X A) k (pairT M (pairT (succ (M + D)) y)) *
          inst2 (sB X A) j (pairT M (pairT (succ (M + D)) y)))
      (inst2 (pB X A) j (pairT M (pairT (succ (M + D)) y)) *
          inst2 (qB X A) k (pairT M (pairT (succ (M + D)) y)) +
        inst2 (pB X A) k (pairT M (pairT (succ (M + D)) y)) *
          inst2 (qB X A) j (pairT M (pairT (succ (M + D)) y))) := by
  have g := pair_alg (hyp.xlc j k y hjk hk) (ab_le hQ hjk hm)
  exact le_congr
    (congrAdd (congrMul (r_at X A j M _ y) (s_at X A k M _ y))
      (congrMul (r_at X A k M _ y) (s_at X A j M _ y))).eqSymm
    (congrAdd (congrMul (p_at X A j M _ y) (q_at X A k M _ y))
      (congrMul (p_at X A k M _ y) (q_at X A j M _ y))).eqSymm g

/-- The diagonal condition: `r_j s_j = p_j q_j`. -/
theorem diag_le (j M m y : PTm n) :
    Γ ⊢[PRAAx] le
      (inst2 (rB X A) j (pairT M (pairT m y)) * inst2 (sB X A) j (pairT M (pairT m y)))
      (inst2 (pB X A) j (pairT M (pairT m y)) * inst2 (qB X A) j (pairT M (pairT m y))) := by
  refine le_of_eq_add (d := zero) ?_
  ipra_lc 𝔞 (inst2 (qB X A) j (pairT M (pairT m y))) * natEq (p_at (Γ := Γ) X A j M m y) +
    (𝔞 (inst2 X (succ j) y) * (𝔞 (gle j M) * 𝔞 (inst2 A (monus M j) y))) * natEq (q_at (Γ := Γ) X A j M m y) -
    𝔞 (inst2 (sB X A) j (pairT M (pairT m y))) * natEq (r_at (Γ := Γ) X A j M m y) -
    (𝔞 (inst2 X j y) * (𝔞 (gle j M) * 𝔞 (inst2 A (monus M j) y))) * natEq (s_at (Γ := Γ) X A j M m y)

/-! ## The four sums -/

theorem shift_add (a b : PTm n) : Syn.shift (a + b) = Syn.shift a + Syn.shift b := by
  simp [Syn.shift]

theorem shift_monus (a b : PTm n) : Syn.shift (monus a b) = monus (Syn.shift a) (Syn.shift b) := by
  simp [Syn.shift]

theorem al_zero {j M m y : PTm n} (h : Γ ⊢[PRAAx] le (succ M) j) :
    Γ ⊢[PRAAx] inst2 (alB A) j (pairT M (pairT m y)) ≐ zero :=
  (al_at A j M m y).eqTrans (mul_eq_zero_of_left (gle_above h))

theorem al_one {j M m y : PTm n} (h : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] inst2 (alB A) j (pairT M (pairT m y)) ≐ inst2 A (monus M j) y :=
  (al_at A j M m y).eqTrans ((congrMul (gle_of_le h) (.eqRefl _)).eqTrans (one_mul _))

/-- `Σ_j p_j = x_0 (M + 1) a_{M+1}`. -/
theorem sum_P (hyp : Hyp X A Nb) {M m y : PTm n} (hMm : Γ ⊢[PRAAx] le M m)
    (hM : Γ ⊢[PRAAx] lt M (bd Nb y)) :
    Γ ⊢[PRAAx] ap2 (sumF (pB X A)) (succ m) (pairT M (pairT m y)) ≐
      inst2 X zero y * (succ M * inst2 A (succ M) y) := by
  have t : Γ ⊢[PRAAx] ap2 (sumF (pB X A)) (succ m) (pairT M (pairT m y)) ≐
      ap2 (sumF (pB X A)) (succ M) (pairT M (pairT m y)) := by
    refine sum_trunc _ (lt_succ_of_le hMm) (.allI (.impI (.impI ?_)))
    simp only [shift_pair, shift_succ]
    rw [pB, inst2_mul]
    exact mul_eq_zero_of_right (al_zero Prf.hyp0)
  have c : Γ ⊢[PRAAx] ap2 (sumF (pB X A)) (succ M) (pairT M (pairT m y)) ≐
      ap2 (sumF (recB X A)) (succ M) (pairT M y) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pair, shift_succ]
    rw [pB, inst2_mul]
    exact (congrMul (x1_at X _ _ _ _) (al_one (le_of_lt_succ Prf.hyp0))).eqTrans
      (rec_at X A _ _ _).eqSymm
  exact t.eqTrans (c.eqTrans (hyp.recur M y hM).eqSymm)

/-- `Σ_j r_j = x_0 (M + 1) a_M`. -/
theorem sum_R (hyp : Hyp X A Nb) {M m y : PTm n} (hMm : Γ ⊢[PRAAx] le M m)
    (hM : Γ ⊢[PRAAx] le M (bd Nb y)) :
    Γ ⊢[PRAAx] ap2 (sumF (rB X A)) (succ m) (pairT M (pairT m y)) ≐
      inst2 X zero y * (succ M * inst2 A M y) := by
  have t : Γ ⊢[PRAAx] ap2 (sumF (rB X A)) (succ m) (pairT M (pairT m y)) ≐
      ap2 (sumF (rB X A)) (succ M) (pairT M (pairT m y)) := by
    refine sum_trunc _ (lt_succ_of_le hMm) (.allI (.impI (.impI ?_)))
    simp only [shift_pair, shift_succ]
    rw [rB, inst2_mul]
    exact mul_eq_zero_of_right (al_zero Prf.hyp0)
  have c : Γ ⊢[PRAAx] ap2 (sumF (rB X A)) (succ M) (pairT M (pairT m y)) ≐
      ap2 (sumF (idB X A)) (succ M) (pairT M y) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pair, shift_succ]
    rw [rB, inst2_mul]
    exact (congrMul (x0_at X _ _ _ _) (al_one (le_of_lt_succ Prf.hyp0))).eqTrans
      (id_at X A _ _ _).eqSymm
  exact t.eqTrans (c.eqTrans (id2 hyp hM).eqSymm)

/-- `Σ_j q_j = x_0 (m + 1) a_m`. -/
theorem sum_Q (hyp : Hyp X A Nb) {M m y : PTm n} (hm : Γ ⊢[PRAAx] le m (bd Nb y)) :
    Γ ⊢[PRAAx] ap2 (sumF (qB X A)) (succ m) (pairT M (pairT m y)) ≐
      inst2 X zero y * (succ m * inst2 A m y) := by
  refine .eqTrans ?_ (id2 hyp hm).eqSymm
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pair, shift_succ]
  exact (q_at X A _ _ _ _).eqTrans (id_at X A _ _ _).eqSymm

/-- `Σ_j s_j = x_0 (m + 1) a_{m+1}`. -/
theorem sum_S (hyp : Hyp X A Nb) {M m y : PTm n} (hm : Γ ⊢[PRAAx] lt m (bd Nb y)) :
    Γ ⊢[PRAAx] ap2 (sumF (sB X A)) (succ m) (pairT M (pairT m y)) ≐
      inst2 X zero y * (succ m * inst2 A (succ m) y) := by
  refine .eqTrans ?_ (hyp.recur m y hm).eqSymm
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pair, shift_succ]
  exact (s_at X A _ _ _ _).eqTrans (rec_at X A _ _ _).eqSymm

/-! ## The domination -/

/-- The pair conditions against a new index `L < N`. -/
theorem pair_all (hyp : Hyp X A Nb) {L M D y : PTm n}
    (hQ : Γ ⊢[PRAAx] allB (oB A Nb) M y ≐ one) (hL : Γ ⊢[PRAAx] lt L (bd Nb y))
    (hm : Γ ⊢[PRAAx] le (succ (M + D)) (bd Nb y)) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift L) ⟶
      le (inst2 (rB X A) (var 0) (Syn.shift (pairT M (pairT (succ (M + D)) y))) *
            inst2 (sB X A) (Syn.shift L) (Syn.shift (pairT M (pairT (succ (M + D)) y))) +
          inst2 (rB X A) (Syn.shift L) (Syn.shift (pairT M (pairT (succ (M + D)) y))) *
            inst2 (sB X A) (var 0) (Syn.shift (pairT M (pairT (succ (M + D)) y))))
        (inst2 (pB X A) (var 0) (Syn.shift (pairT M (pairT (succ (M + D)) y))) *
            inst2 (qB X A) (Syn.shift L) (Syn.shift (pairT M (pairT (succ (M + D)) y))) +
          inst2 (pB X A) (Syn.shift L) (Syn.shift (pairT M (pairT (succ (M + D)) y))) *
            inst2 (qB X A) (var 0) (Syn.shift (pairT M (pairT (succ (M + D)) y))))) := by
  refine .allI (.impI ?_)
  have hQ' : (Γ.map Fm.shift) ⊢[PRAAx] allB (oB A Nb) (Syn.shift M) (Syn.shift y) ≐ one := by
    simpa [Fm.shift, Syn.shift] using hQ.shift
  have hL' : (Γ.map Fm.shift) ⊢[PRAAx] lt (Syn.shift L) (Syn.shift (bd Nb y)) := by
    simpa [Fm.shift, Syn.shift] using hL.shift
  have hm' : (Γ.map Fm.shift) ⊢[PRAAx]
      le (succ (Syn.shift M + Syn.shift D)) (Syn.shift (bd Nb y)) := by
    simpa [Fm.shift, Syn.shift] using hm.shift
  rw [shift_bd] at hL' hm'
  simp only [shift_pair, shift_succ, shift_add]
  exact pair_le hyp hQ'.wk Prf.hyp0 hL'.wk hm'.wk

variable (X A)

/-- The induction formula of `dom_all`; variable `0` is the upper limit. -/
abbrev domF (M D y : PTm n) : Fm PTm (n + 1) :=
  le (var 0) (succ (succ (Syn.shift M + Syn.shift D))) ⟶
    le (ap2 (sumF (rB X A)) (var 0)
          (pairT (Syn.shift M) (pairT (succ (Syn.shift M + Syn.shift D)) (Syn.shift y))) *
        ap2 (sumF (sB X A)) (var 0)
          (pairT (Syn.shift M) (pairT (succ (Syn.shift M + Syn.shift D)) (Syn.shift y))))
      (ap2 (sumF (pB X A)) (var 0)
          (pairT (Syn.shift M) (pairT (succ (Syn.shift M + Syn.shift D)) (Syn.shift y))) *
        ap2 (sumF (qB X A)) (var 0)
          (pairT (Syn.shift M) (pairT (succ (Syn.shift M + Syn.shift D)) (Syn.shift y))))

variable {X A}

/-- `(Σ r)(Σ s) ≤ (Σ p)(Σ q)` over the indices `j ≤ m = M + D + 1`. -/
theorem dom_all (hyp : Hyp X A Nb) {M D y : PTm n}
    (hQ : Γ ⊢[PRAAx] allB (oB A Nb) M y ≐ one)
    (hm : Γ ⊢[PRAAx] lt (succ (M + D)) (bd Nb y)) :
    Γ ⊢[PRAAx] le
      (ap2 (sumF (rB X A)) (succ (succ (M + D))) (pairT M (pairT (succ (M + D)) y)) *
        ap2 (sumF (sB X A)) (succ (succ (M + D))) (pairT M (pairT (succ (M + D)) y)))
      (ap2 (sumF (pB X A)) (succ (succ (M + D))) (pairT M (pairT (succ (M + D)) y)) *
        ap2 (sumF (qB X A)) (succ (succ (M + D))) (pairT M (pairT (succ (M + D)) y))) := by
  have hall : Γ ⊢[PRAAx] Fm.all (domF X A M D y) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · have b : Γ ⊢[PRAAx] le zero (succ (succ (M + D))) ⟶
          le (ap2 (sumF (rB X A)) zero (pairT M (pairT (succ (M + D)) y)) *
              ap2 (sumF (sB X A)) zero (pairT M (pairT (succ (M + D)) y)))
            (ap2 (sumF (pB X A)) zero (pairT M (pairT (succ (M + D)) y)) *
              ap2 (sumF (qB X A)) zero (pairT M (pairT (succ (M + D)) y))) := by
        refine .impI (le_of_eq_add (d := zero) ?_)
        have e₁ := natEq (sum_zero (Γ := le zero (succ (succ (M + D))) :: Γ) (rB X A)
          (pairT M (pairT (succ (M + D)) y)))
        have e₃ := natEq (sum_zero (Γ := le zero (succ (succ (M + D))) :: Γ) (pB X A)
          (pairT M (pairT (succ (M + D)) y)))
        apply deriveNat; ipra_simps
        rw [e₁, e₃]; ring
      simpa using b
    · have hQ' : (Γ.map Fm.shift) ⊢[PRAAx]
          allB (oB A Nb) (Syn.shift M) (Syn.shift y) ≐ one := by
        simpa [Fm.shift, Syn.shift] using hQ.shift
      have hm' : (Γ.map Fm.shift) ⊢[PRAAx]
          lt (succ (Syn.shift M + Syn.shift D)) (Syn.shift (bd Nb y)) := by
        simpa [Fm.shift, Syn.shift] using hm.shift
      rw [shift_bd] at hm'
      have st : (domF X A M D y :: Γ.map Fm.shift) ⊢[PRAAx]
          le (succ (var 0)) (succ (succ (Syn.shift M + Syn.shift D))) ⟶
            le (ap2 (sumF (rB X A)) (succ (var 0))
                  (pairT (Syn.shift M) (pairT (succ (Syn.shift M + Syn.shift D)) (Syn.shift y))) *
                ap2 (sumF (sB X A)) (succ (var 0))
                  (pairT (Syn.shift M) (pairT (succ (Syn.shift M + Syn.shift D)) (Syn.shift y))))
              (ap2 (sumF (pB X A)) (succ (var 0))
                  (pairT (Syn.shift M) (pairT (succ (Syn.shift M + Syn.shift D)) (Syn.shift y))) *
                ap2 (sumF (qB X A)) (succ (var 0))
                  (pairT (Syn.shift M)
                    (pairT (succ (Syn.shift M + Syn.shift D)) (Syn.shift y)))) := by
        refine .impI ?_
        have hL : (le (succ (var 0)) (succ (succ (Syn.shift M + Syn.shift D))) ::
            domF X A M D y :: Γ.map Fm.shift) ⊢[PRAAx]
            le (succ (var 0)) (succ (succ (Syn.shift M + Syn.shift D))) := Prf.hyp0
        have ih := Prf.impE (Prf.hyp1 (Γ := Γ.map Fm.shift) (φ := domF X A M D y)
          (ψ := le (succ (var 0)) (succ (succ (Syn.shift M + Syn.shift D)))))
          (le_trans (le_succ_self _) hL)
        have hLN : (le (succ (var 0)) (succ (succ (Syn.shift M + Syn.shift D))) ::
            domF X A M D y :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (bd Nb (Syn.shift y)) :=
          lt_of_le_of_lt (le_of_lt_succ hL) hm'.wk.wk
        exact dom_step _ _ _ _ ih (diag_le _ _ _ _)
          (pair_all hyp hQ'.wk.wk hLN (le_of_lt hm'.wk.wk))
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE (succ (succ (M + D))) hall
  have h3 : Γ ⊢[PRAAx] le (succ (succ (M + D))) (succ (succ (M + D))) ⟶
      le (ap2 (sumF (rB X A)) (succ (succ (M + D))) (pairT M (pairT (succ (M + D)) y)) *
          ap2 (sumF (sB X A)) (succ (succ (M + D))) (pairT M (pairT (succ (M + D)) y)))
        (ap2 (sumF (pB X A)) (succ (succ (M + D))) (pairT M (pairT (succ (M + D)) y)) *
          ap2 (sumF (qB X A)) (succ (succ (M + D))) (pairT M (pairT (succ (M + D)) y))) := by
    simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2
  exact .impE h3 (le_refl _)

/-! ## The inequality at one pair, and the induction -/

/-- The statement at `(M, D)` from the statement for all `μ < M`. -/
theorem lc_main (hyp : Hyp X A Nb) {M D y : PTm n}
    (hQ : Γ ⊢[PRAAx] allB (oB A Nb) M y ≐ one)
    (hm : Γ ⊢[PRAAx] lt (succ (M + D)) (bd Nb y)) :
    Γ ⊢[PRAAx] le (inst2 A M y * inst2 A (succ (succ (M + D))) y)
      (inst2 A (succ M) y * inst2 A (succ (M + D)) y) := by
  have hMm : Γ ⊢[PRAAx] le M (succ (M + D)) :=
    le_of_eq_add (d := succ D) (by ipra_ring)
  have hMN : Γ ⊢[PRAAx] lt M (bd Nb y) := lt_of_le_of_lt hMm hm
  have d := dom_all hyp hQ hm
  have eP := natEq (sum_P hyp hMm hMN)
  have eQ := natEq (sum_Q (M := M) hyp (le_of_lt hm))
  have eR := natEq (sum_R hyp hMm (le_of_lt hMN))
  have eS := natEq (sum_S (M := M) hyp hm)
  have hx : Γ ⊢[PRAAx] inst2 X zero y ≐ succ (pred (inst2 X zero y)) :=
    .orE (zero_or_succ _) (lt_irrefl zero _ (lt_congr (.eqRefl _) Prf.hyp0 (hyp.pos y))) Prf.hyp0
  have ex := natEq hx
  have big : Γ ⊢[PRAAx]
      le (succ (pred (inst2 X zero y)) * (succ (pred (inst2 X zero y)) * (succ M *
          (succ (succ (M + D)) * (inst2 A M y * inst2 A (succ (succ (M + D))) y)))))
        (succ (pred (inst2 X zero y)) * (succ (pred (inst2 X zero y)) * (succ M *
          (succ (succ (M + D)) * (inst2 A (succ M) y * inst2 A (succ (M + D)) y))))) := by
    refine le_congr ?_ ?_ d
    · apply deriveNat; ipra_simps
      rw [eR, eS, ex]; ring
    · apply deriveNat; ipra_simps
      rw [eP, eQ, ex]; ring
  exact mul_le_cancel (mul_le_cancel (mul_le_cancel (mul_le_cancel big)))

theorem delta_rev {μ δ N : PTm n} (h : Γ ⊢[PRAAx] lt δ (monus N (succ μ))) :
    Γ ⊢[PRAAx] lt (succ (μ + δ)) N := by
  refine .orE (le_total (succ μ) N) ?_ ?_
  · have e₁ := natEq (eq_add_of_le (Prf.hyp0 (Γ := Γ) (φ := le (succ μ) N)))
    have e₂ := natEq (eq_add_of_le (h.wk (ψ := le (succ μ) N)))
    exact le_of_eq_add (d := monus (monus N (succ μ)) (succ δ))
      (by apply deriveNat; ipra_simps; linear_combination e₁ + e₂)
  · have z : (le N (succ μ) :: Γ) ⊢[PRAAx] monus N (succ μ) ≐ zero := Prf.hyp0
    exact lt_zero_absurd _ (lt_congr (.eqRefl _) z (h.wk (ψ := le N (succ μ))))

/-- The bit at `M` from the bit for all `μ < M`. -/
theorem o_one (hyp : Hyp X A Nb) {M y : PTm n} (hQ : Γ ⊢[PRAAx] allB (oB A Nb) M y ≐ one) :
    Γ ⊢[PRAAx] inst2 (oB A Nb) M y ≐ one := by
  rw [inst2_oB]
  refine all_intro (iB A) (.allI (.impI ?_))
  have hQ' : (Γ.map Fm.shift) ⊢[PRAAx] allB (oB A Nb) (Syn.shift M) (Syn.shift y) ≐ one := by
    simpa [Fm.shift, Syn.shift] using hQ.shift
  simp only [shift_pair, shift_succ, shift_monus, shift_bd]
  have hm := delta_rev (Prf.hyp0 (Γ := Γ.map Fm.shift)
    (φ := lt (var 0) (monus (bd Nb (Syn.shift y)) (succ (Syn.shift M)))))
  exact ne_of_one ((i_at A _ _ _).eqTrans (gle_of_le (lc_main hyp hQ'.wk hm)))

variable (A Nb)

/-- The induction formula of `lc_all`; variable `0 = M`. -/
abbrev allF (y : PTm n) : Fm PTm (n + 1) := allB (oB A Nb) (var 0) (Syn.shift y) ≐ one

variable {A Nb}

/-- The statement for all `μ < M` and all admissible `δ`, for every `M`. -/
theorem lc_all (hyp : Hyp X A Nb) (M y : PTm n) : Γ ⊢[PRAAx] allB (oB A Nb) M y ≐ one := by
  have hall : Γ ⊢[PRAAx] Fm.all (allF A Nb y) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa using allB_zero (Γ := Γ) (oB A Nb) y
    · have st : (allF A Nb y :: Γ.map Fm.shift) ⊢[PRAAx]
          allB (oB A Nb) (succ (var 0)) (Syn.shift y) ≐ one :=
        allB_extend (oB A Nb) Prf.hyp0 (o_one hyp Prf.hyp0)
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE M hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2

/-- `lem:coefficient-logconcave`: `a_{m−1} a_{n+1} ≤ a_m a_n` for `1 ≤ m ≤ n`, `n + 1 ≤ N`, with
`m = μ + 1` and `n = μ + δ + 1`. -/
theorem coefficient_logconcave (hyp : Hyp X A Nb) (μ δ y : PTm n)
    (h : Γ ⊢[PRAAx] lt (succ (μ + δ)) (bd Nb y)) :
    Γ ⊢[PRAAx] le (inst2 A μ y * inst2 A (succ (succ (μ + δ))) y)
      (inst2 A (succ μ) y * inst2 A (succ (μ + δ)) y) :=
  lc_main hyp (lc_all hyp μ y) h

end General

end LeanProofs.IPRA.Combinatorics.CoefficientLogConcave
