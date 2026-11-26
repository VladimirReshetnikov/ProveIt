import IPRADerivations.Core.Search
import IPRADerivations.Core.MultiSums
import IPRADerivations.Foundations.GapDecision
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# Exact label recovery from a separation gap

The finite-label gap theorems of the framework packets:

* `foundations/cifer_ipra_framework_2026-11-15`, `thm:gap-collapse`;
* `foundations/ipra_frnf_framework_bundle`, `thm:gap-collapse`;
* `foundations/ipra_finite_query_normal_form_2026-11-16`, `thm:gap-recovery`;
* `foundations/ipra_native_clause_framework_2026-11-15`, `thm:gap`;

and the sign form `foundations/ipra_embedding_framework_2026-11-15`, `thm:exact-gap`.

Labels `i < M` sit in a metric presentation, scaled to natural numbers: `δ(i, y)` is the distance
from the observation `y` to label `i` and `D(i, j, y)` the distance between labels `i`, `j`. The
hypotheses are object-level iPRA formulas: the triangle inequality through the observation,
`D(i, j) ≤ δ(i) + δ(j)`, and separation, `i ≠ j → 2e < D(i, j)` for `i, j < M`.

* `pass_unique`: two labels within `e` of the observation coincide;
* `gap_recover`: if some `i₀ < M` is within `e`, the bounded search `μ_{i<M} [δ(i) ≤ e]` returns
  exactly `i₀`; in particular every valid candidate recovers the same label;
* `exact_gap_above`, `exact_gap_below` (`thm:exact-gap`, on the integer line, `abs` as in
  `Foundations/GapDecision`): if `x ≥ q + d` (resp. `x + d ≤ q`) and `2 abs (a − x) < d`, then
  `a > q` (resp. `a < q`), so the rational sign of `a − q` is that of `x − q` and nonzero.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.GapRecovery

open_ipra
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_tri zabs_neg)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

variable (δ : PTm 2) (D : PTm 3)

/-- Two labels within `e` of the observation coincide. -/
theorem pass_unique {i j y e : PTm n} (hi : Γ ⊢[PRAAx] le (inst2 δ i y) e)
    (hj : Γ ⊢[PRAAx] le (inst2 δ j y) e)
    (htri : Γ ⊢[PRAAx] le (inst3 D i j y) (inst2 δ i y + inst2 δ j y))
    (hsep : Γ ⊢[PRAAx] neg (i ≐ j) ⟶ lt (two * e) (inst3 D i j y)) : Γ ⊢[PRAAx] i ≐ j := by
  refine .orE (eq_or_ne i j) Prf.hyp0 ?_
  have s := Prf.impE hsep.wk Prf.hyp0
  have b : Γ ⊢[PRAAx] le (inst2 δ i y + inst2 δ j y) (two * e) := by
    refine le_of_eq_add (d := monus e (inst2 δ i y) + monus e (inst2 δ j y)) ?_
    ipra_lc natEq (eq_add_of_le hi) + natEq (eq_add_of_le hj)
  exact le_lt_absurd _ (le_trans htri.wk b.wk) s

/-- The pass test `δ(i, snd z) ∸ fst z`, zero exactly when label `i` is within `e = fst z`. -/
def passB : PTm 2 := monus (Syn.subst ![var 0, sndT (var 1)] δ) (fstT (var 1))

theorem inst2_pass (i z : PTm n) : inst2 (passB δ) i z = monus (inst2 δ i (sndT z)) (fstT z) := by
  simp only [inst2, passB, PTm.subst_monus, subst_fstT, Syn.subst_subst]
  congr 2
  funext k; fin_cases k <;> simp

theorem pass_at (i e y : PTm n) : Γ ⊢[PRAAx] inst2 (passB δ) i (pairT e y) ≐ monus (inst2 δ i y) e := by
  rw [inst2_pass]
  exact congrMonus (congrInst2 δ (.eqRefl i) (snd_pair e y)) (fst_pair e y)

/-- The recovered label `μ_{i<M} [δ(i, y) ≤ e]`. -/
abbrev labT (M e y : PTm n) : PTm n := Search.mu (passB δ) M (pairT e y)

theorem subst_up_shift_gr {m : ℕ} (σ : Fin n → PTm m) (t : PTm n) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  rw [Syn.subst_shift, Syn.shift_subst]; simp

theorem subst_sh2' (t i j : PTm n) :
    Syn.subst (Syn.inst j) (Syn.subst (Syn.up (Syn.inst i)) (Syn.shift (Syn.shift t))) = t := by
  rw [subst_up_shift_gr]; simp

/-- The separation hypothesis: `i, j < M`, `i ≠ j` give `2e < D(i, j, y)`. -/
abbrev SepF (M e y : PTm n) : Fm PTm n :=
  Fm.all (Fm.all (lt (var 1) (Syn.shift (Syn.shift M)) ⟶ (lt (var 0) (Syn.shift (Syn.shift M)) ⟶
    (neg (var 1 ≐ var 0) ⟶ lt (two * Syn.shift (Syn.shift e)) (inst3 D (var 1) (var 0) (Syn.shift (Syn.shift y)))))))

/-- The triangle inequality through the observation: `D(i, j, y) ≤ δ(i, y) + δ(j, y)`. -/
abbrev TriF (y : PTm n) : Fm PTm n :=
  Fm.all (Fm.all (le (inst3 D (var 1) (var 0) (Syn.shift (Syn.shift y)))
    (inst2 δ (var 1) (Syn.shift (Syn.shift y)) + inst2 δ (var 0) (Syn.shift (Syn.shift y)))))

theorem sep_at {M e y : PTm n} (h : Γ ⊢[PRAAx] SepF D M e y) (i j : PTm n) :
    Γ ⊢[PRAAx] lt i M ⟶ (lt j M ⟶ (neg (i ≐ j) ⟶ lt (two * e) (inst3 D i j y))) := by
  have a := Prf.allE j (Prf.allE i h)
  simpa [subst_sh2', subst_inst3] using a

theorem tri_at {y : PTm n} (h : Γ ⊢[PRAAx] TriF δ D y) (i j : PTm n) :
    Γ ⊢[PRAAx] le (inst3 D i j y) (inst2 δ i y + inst2 δ j y) := by
  have a := Prf.allE j (Prf.allE i h)
  simpa [subst_sh2', subst_inst3, subst_inst2] using a

/-- Any two labels `< M` within `e` of the observation coincide. -/
theorem passing_unique {M e y i j : PTm n} (hsep : Γ ⊢[PRAAx] SepF D M e y) (htri : Γ ⊢[PRAAx] TriF δ D y)
    (hiM : Γ ⊢[PRAAx] lt i M) (hjM : Γ ⊢[PRAAx] lt j M)
    (hi : Γ ⊢[PRAAx] le (inst2 δ i y) e) (hj : Γ ⊢[PRAAx] le (inst2 δ j y) e) : Γ ⊢[PRAAx] i ≐ j :=
  pass_unique δ D hi hj (tri_at δ D htri i j) (Prf.impE (Prf.impE (sep_at D hsep i j) hiM) hjM)

/-- Exact recovery: if `i₀ < M` is within `e` of the observation, the bounded search returns `i₀`,
and the label it returns is within `e`. -/
theorem gap_recover {M e y i₀ : PTm n} (hsep : Γ ⊢[PRAAx] SepF D M e y) (htri : Γ ⊢[PRAAx] TriF δ D y)
    (hM : Γ ⊢[PRAAx] lt i₀ M) (hp : Γ ⊢[PRAAx] le (inst2 δ i₀ y) e) :
    Γ ⊢[PRAAx] (labT δ M e y ≐ i₀) ⋏ le (inst2 δ (labT δ M e y) y) e := by
  have s := Search.search_found (f := passB δ) ((pass_at δ i₀ e y).eqTrans hp) hM
  have hL : Γ ⊢[PRAAx] le (inst2 δ (labT δ M e y) y) e :=
    (pass_at δ _ e y).eqSymm.eqTrans (Prf.andE₁ (Prf.andE₂ s))
  exact .andI (passing_unique δ D hsep htri (Prf.andE₁ s) hM hL hp) hL

/-! ## The sign form on the integer line -/

/-- `u + abs u = 2 (u⁺ ∸ u⁻)`. -/
theorem abs_add (u : ZT n) :
    ZT.toZ Γ u + 𝔞 (zabs u) = 2 * 𝔞 (monus u.pos u.neg) := by
  have e := natEq (monus_max (Γ := Γ) u.pos u.neg)
  rw [toZ_def]
  simp only [zabs, LeanProofs.IPRA.Probability.Variance.ad, Q.mk_add, map_add] at e ⊢
  linear_combination -e

/-- `−u + abs u = 2 (u⁻ ∸ u⁺)`. -/
theorem abs_sub (u : ZT n) :
    -ZT.toZ Γ u + 𝔞 (zabs u) = 2 * 𝔞 (monus u.neg u.pos) := by
  have e := natEq (monus_max (Γ := Γ) u.pos u.neg)
  rw [toZ_def]
  simp only [zabs, LeanProofs.IPRA.Probability.Variance.ad, Q.mk_add, map_add] at e ⊢
  linear_combination e

variable {x q a : ZT n} {d : PTm n}

/-- `thm:exact-gap`, upper branch: `x ≥ q + d` and `2 abs (a − x) < d` give `a ≥ q + 1`. -/
theorem exact_gap_above (hx : Γ ⊢[PRAAx] zle (q + ZT.ofNat d) x)
    (ha : Γ ⊢[PRAAx] lt (two * zabs (a - x)) d) : Γ ⊢[PRAAx] zle (q + ZT.natLit 1) a := by
  have h1 := zle_toZ hx
  have h2 := natEq (eq_add_of_le ha)
  have h3 := abs_add (Γ := Γ) (a - x)
  refine zle_of_toZ (zabs (a - x) + monus d (succ (two * zabs (a - x))) +
    monus (x.pos + (q + ZT.ofNat d).neg) ((q + ZT.ofNat d).pos + x.neg) +
    two * monus (a - x).pos (a - x).neg) ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_ofNat, ZT.toZ_natLit] at h1 h3 ⊢
  ipra_simps
  linear_combination h1 - h2 - h3

/-- `thm:exact-gap`, lower branch: `x + d ≤ q` and `2 abs (a − x) < d` give `a + 1 ≤ q`. -/
theorem exact_gap_below (hx : Γ ⊢[PRAAx] zle (x + ZT.ofNat d) q)
    (ha : Γ ⊢[PRAAx] lt (two * zabs (a - x)) d) : Γ ⊢[PRAAx] zle (a + ZT.natLit 1) q := by
  have h1 := zle_toZ hx
  have h2 := natEq (eq_add_of_le ha)
  have h4 := abs_sub (Γ := Γ) (a - x)
  refine zle_of_toZ (zabs (a - x) + monus d (succ (two * zabs (a - x))) +
    monus (q.pos + (x + ZT.ofNat d).neg) ((x + ZT.ofNat d).pos + q.neg) +
    two * monus (a - x).neg (a - x).pos) ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_ofNat, ZT.toZ_natLit] at h1 h4 ⊢
  ipra_simps
  linear_combination h1 - h2 - h4

end LeanProofs.IPRA.Foundations.GapRecovery
