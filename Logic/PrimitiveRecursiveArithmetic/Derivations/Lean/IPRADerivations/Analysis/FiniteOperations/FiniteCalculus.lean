import IPRADerivations.Core.SumOrder

/-!
# Finite calculus: summed increments and the cell error of a rectangle sum

Packet: `analytic-number-theory/zeta_functional_equation_ipra` (`lem:finitecalculus`). The lemma
is used through two finite facts about samples `F(0), F(1), …` on a subdivision.

* `increments_le`: if `F(j + 1) ≤ F(j) + g(j)` for `j < N`, then `F(i) ≤ F(0) + ∑_{j<i} g(j)`
  for `i ≤ N`. With `g(j)` the main term plus the Taylor error of cell `j`, this is the passage
  from the estimate on each cell to `eq:telescoping`: "use the Taylor estimate on each cell and
  add";
* `lip_up`: if `f(j + 1) ≤ f(j) + D` for `j < N` (a Lipschitz bound for samples at equal
  spacing), then `f(i) ≤ f(0) + D i` for `i ≤ N`;
* `lin_sum`: `2 ∑_{i<r} (c + D i) + D r = 2 r c + D r²`;
* `cell_upper`: under the same hypothesis on a cell with `r` samples,
  `2 ∑_{i<r} f(i) + D r ≤ 2 r f(0) + D r²`: the refined rectangle sum exceeds the coarse one
  `r f(0)` by at most `D r (r − 1)/2`. With sample spacing `h/r` this is the bound
  "the total change on a cell of width `h` is at most `D h²/2`" of the proof.

* `lip_down`, `cell_lower`: the lower bounds, from `f(j) ≤ f(j + 1) + D`:
  `f(0) ≤ f(i) + D i` and `2 r f(0) + D r ≤ 2 ∑_{i<r} f(i) + D r²`.

The integral names, the Taylor estimates of the elementary
functions and the functional equation are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.FiniteCalculus

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Summed increments -/

/-- If `F(j + 1) ≤ F(j) + g(j)` for `j < N`, then `F(i) ≤ F(0) + ∑_{j<i} g(j)` for `i ≤ N`. -/
theorem increments_le (F g : PTm 2) (x N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 F (succ (var 0)) (Syn.shift x)) (inst2 F (var 0) (Syn.shift x) + inst2 g (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (inst2 F (var 0) (Syn.shift x)) (inst2 F zero (Syn.shift x) + ap2 (sumF g) (var 0) (Syn.shift x))) := by
  ipra_qfind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2, subst_inst2]
  · exact .impI (le_add_right _ _)
  · have hf := h.allOpen
    refine .impI ?_
    have hle : (le (succ (var 0)) (Syn.shift N) ::
        (le (var 0) (Syn.shift N) ⟶ le (inst2 F (var 0) (Syn.shift x))
          (inst2 F zero (Syn.shift x) + ap2 (sumF g) (var 0) (Syn.shift x))) ::
        Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
      le_trans (le_succ_self _) Prf.hyp0
    have ih := Prf.impE Prf.hyp1 hle
    refine le_trans (Prf.impE hf.wk.wk Prf.hyp0) ?_
    exact le_congr (.eqRefl _)
      ((add_assoc _ _ _).eqTrans (congrAdd (.eqRefl _) (sum_succ' g (var 0) _).eqSymm))
      (add_le_add_right (inst2 g (var 0) (Syn.shift x)) ih)

/-! ## A Lipschitz bound for equally spaced samples -/

theorem lin_step (a D i : PTm n) : Γ ⊢[PRAAx] (a + D * i) + D ≐ a + D * succ i := by
  ipra_ring

/-- If `f(j + 1) ≤ f(j) + D` for `j < N`, then `f(i) ≤ f(0) + D i` for `i ≤ N`. -/
theorem lip_up (f : PTm 2) (x N D : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 f (succ (var 0)) (Syn.shift x)) (inst2 f (var 0) (Syn.shift x) + Syn.shift D))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (inst2 f (var 0) (Syn.shift x)) (inst2 f zero (Syn.shift x) + Syn.shift D * var 0)) := by
  ipra_qfind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_inst2]
  · exact .impI (le_add_right _ _)
  · have hf := h.allOpen
    refine .impI ?_
    have hle : (le (succ (var 0)) (Syn.shift N) ::
        (le (var 0) (Syn.shift N) ⟶ le (inst2 f (var 0) (Syn.shift x))
          (inst2 f zero (Syn.shift x) + Syn.shift D * var 0)) ::
        Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
      le_trans (le_succ_self _) Prf.hyp0
    have ih := Prf.impE Prf.hyp1 hle
    refine le_trans (Prf.impE hf.wk.wk Prf.hyp0) ?_
    exact le_congr (.eqRefl _) (lin_step _ _ _) (add_le_add_right (Syn.shift D) ih)

/-! ## The sum of a linear sequence -/

/-- `c + D i`, with the parameter `⟨c, D⟩`. -/
abbrev linB : PTm 2 := fstT (var 1) + sndT (var 1) * var 0

theorem inst2_lin (i y : PTm n) : inst2 linB i y = fstT y + sndT y * i := by simp [inst2]

theorem lin_base (c D : PTm n) :
    Γ ⊢[PRAAx] two * ap2 (sumF linB) zero (pairT c D) + D * zero ≐ two * (zero * c) + D * (zero * zero) := by
  ipra_lc 2 * natEq (sum_zero (Γ := Γ) linB (pairT c D))

theorem lin_succ {r c D : PTm n}
    (ih : Γ ⊢[PRAAx] two * ap2 (sumF linB) r (pairT c D) + D * r ≐ two * (r * c) + D * (r * r)) :
    Γ ⊢[PRAAx] two * ap2 (sumF linB) (succ r) (pairT c D) + D * succ r ≐
      two * (succ r * c) + D * (succ r * succ r) := by
  have e := sum_succ' (Γ := Γ) linB r (pairT c D)
  rw [inst2_lin] at e
  have t : Γ ⊢[PRAAx] fstT (pairT c D) + sndT (pairT c D) * r ≐ c + D * r :=
    congrAdd (fst_pair _ _) (congrMul (snd_pair _ _) (.eqRefl _))
  ipra_lc 2 * natEq (e.eqTrans (congrAdd (.eqRefl _) t)) + natEq ih

/-- Variables: `0 = r` (induction), `1 = c`, `2 = D`. -/
private abbrev linF : Fm PTm 3 :=
  two * ap2 (sumF linB) (var 0) (pairT (var 1) (var 2)) + var 2 * var 0 ≐
    two * (var 0 * var 1) + var 2 * (var 0 * var 0)

private theorem lin₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] linF := by
  ipra_ind [subst_ap2, subst_pairT]
  · exact lin_base _ _
  · exact lin_succ Prf.hyp0

/-- `2 ∑_{i<r} (c + D i) + D r = 2 r c + D r²`. -/
theorem lin_sum (r c D : PTm n) :
    Γ ⊢[PRAAx] two * ap2 (sumF linB) r (pairT c D) + D * r ≐ two * (r * c) + D * (r * r) := by
  have h := inst (Γ := Γ) lin₀ (![r, c, D] : Fin 3 → PTm n)
  simpa using h

/-! ## The cell error -/

theorem two_mul_le_two_mul {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (two * a) (two * b) :=
  le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right two h)

/-- `2 ∑_{i<r} f(i) + D r ≤ 2 r f(0) + D r²` when `f(j + 1) ≤ f(j) + D` for `j < r`. -/
theorem cell_upper (f : PTm 2) (x r D : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift r) ⟶
      le (inst2 f (succ (var 0)) (Syn.shift x)) (inst2 f (var 0) (Syn.shift x) + Syn.shift D))) :
    Γ ⊢[PRAAx] le (two * ap2 (sumF f) r x + D * r) (two * (r * inst2 f zero x) + D * (r * r)) := by
  have lipO := (lip_up f x r D h).allOpen
  have hs : Γ ⊢[PRAAx] le (ap2 (sumF f) r x) (ap2 (sumF linB) r (pairT (inst2 f zero x) D)) := by
    refine sum_le_params f linB x (pairT (inst2 f zero x) D) r (.allI (.impI ?_))
    have e : Syn.shift (pairT (inst2 f zero x) D) = pairT (inst2 f zero (Syn.shift x)) (Syn.shift D) := by
      simp [Syn.shift, subst_inst2]
    rw [e, inst2_lin]
    exact le_congr (.eqRefl _)
      (congrAdd (fst_pair _ _).eqSymm (congrMul (snd_pair _ _).eqSymm (.eqRefl _)))
      (Prf.impE lipO.wk (le_of_lt Prf.hyp0))
  exact le_congr (.eqRefl _) (lin_sum r (inst2 f zero x) D)
    (add_le_add_right (D * r) (two_mul_le_two_mul hs))

/-! ## Lower bounds -/

theorem lin_step' (a D i : PTm n) : Γ ⊢[PRAAx] (a + D) + D * i ≐ a + D * succ i := by
  ipra_ring

/-- If `f(j) ≤ f(j + 1) + D` for `j < N`, then `f(0) ≤ f(i) + D i` for `i ≤ N`. -/
theorem lip_down (f : PTm 2) (x N D : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 f (var 0) (Syn.shift x)) (inst2 f (succ (var 0)) (Syn.shift x) + Syn.shift D))) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (inst2 f zero (Syn.shift x)) (inst2 f (var 0) (Syn.shift x) + Syn.shift D * var 0)) := by
  ipra_qfind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_inst2]
  · exact .impI (le_add_right _ _)
  · have hf := h.allOpen
    refine .impI ?_
    have hle : (le (succ (var 0)) (Syn.shift N) ::
        (le (var 0) (Syn.shift N) ⟶ le (inst2 f zero (Syn.shift x))
          (inst2 f (var 0) (Syn.shift x) + Syn.shift D * var 0)) ::
        Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
      le_trans (le_succ_self _) Prf.hyp0
    have ih := Prf.impE Prf.hyp1 hle
    refine le_trans ih ?_
    exact le_congr (.eqRefl _) (lin_step' _ _ _)
      (add_le_add_right (Syn.shift D * var 0) (Prf.impE hf.wk.wk Prf.hyp0))

/-- `f(i, fst y)`: the body `f` read at the first component of a pair parameter. -/
abbrev fp (f : PTm 2) : PTm 2 := Syn.subst ![var 0, fstT (var 1)] f
/-- `snd y · i`. -/
abbrev linZ : PTm 2 := sndT (var 1) * var 0

theorem inst2_fp (f : PTm 2) (i y : PTm n) : inst2 (fp f) i y = inst2 f i (fstT y) := by
  simp only [inst2, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

theorem inst2_linZ (i y : PTm n) : inst2 linZ i y = sndT y * i := by simp [inst2]

/-- `2 r f(0) + D r ≤ 2 ∑_{i<r} f(i) + D r²` when `f(j) ≤ f(j + 1) + D` for `j < r`: the refined
rectangle sum is below the coarse one `r f(0)` by at most `D r (r − 1)/2`. -/
theorem cell_lower (f : PTm 2) (x r D : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift r) ⟶
      le (inst2 f (var 0) (Syn.shift x)) (inst2 f (succ (var 0)) (Syn.shift x) + Syn.shift D))) :
    Γ ⊢[PRAAx] le (two * (r * inst2 f zero x) + D * r) (two * ap2 (sumF f) r x + D * (r * r)) := by
  have lipO := (lip_down f x r D h).allOpen
  have e₁ : Syn.shift (pairT (inst2 f zero x) zero) = pairT (inst2 f zero (Syn.shift x)) zero := by
    simp [Syn.shift, subst_inst2]
  have e₂ : Syn.shift (pairT x D) = pairT (Syn.shift x) (Syn.shift D) := by simp [Syn.shift]
  have e₃ : Syn.shift (pairT (zero : PTm n) D) = pairT zero (Syn.shift D) := by simp [Syn.shift]
  have s₁ : Γ ⊢[PRAAx] le (ap2 (sumF linB) r (pairT (inst2 f zero x) zero))
      (ap2 (sumF (addBody (fp f) linZ)) r (pairT x D)) := by
    refine sum_le_params _ _ _ _ _ (.allI (.impI ?_))
    rw [e₁, e₂, inst2_lin, inst2_addBody, inst2_fp, inst2_linZ]
    exact le_congr
      ((congrAdd (fst_pair _ _) ((congrMul (snd_pair _ _) (.eqRefl _)).eqTrans (zero_mul _))).eqTrans
        (add_zero _)).eqSymm
      (congrAdd (congrInst2 f (.eqRefl _) (fst_pair _ _)) (congrMul (snd_pair _ _) (.eqRefl _))).eqSymm
      (Prf.impE lipO.wk (le_of_lt Prf.hyp0))
  have c₁ : Γ ⊢[PRAAx] ap2 (sumF (fp f)) r (pairT x D) ≐ ap2 (sumF f) r x := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [e₂, inst2_fp]
    exact congrInst2 f (.eqRefl _) (fst_pair _ _)
  have c₂ : Γ ⊢[PRAAx] ap2 (sumF linZ) r (pairT x D) ≐ ap2 (sumF linB) r (pairT zero D) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [e₂, e₃, inst2_linZ, inst2_lin]
    exact (congrMul (snd_pair _ _) (.eqRefl _)).eqTrans
      ((congrAdd (fst_pair _ _) (congrMul (snd_pair _ _) (.eqRefl _))).eqTrans (zero_add _)).eqSymm
  have b₁ := natEq c₁; have b₂ := natEq c₂
  refine le_congr ?_ ?_ (add_le_add_right (D * r) (two_mul_le_two_mul s₁))
  · ipra_lc natEq (lin_sum (Γ := Γ) r (inst2 f zero x) zero)
  · ipra_lc 2 * natEq (sum_add (Γ := Γ) (fp f) linZ r (pairT x D)) + 2 * b₁ + 2 * b₂ +
      natEq (lin_sum (Γ := Γ) r zero D)

end LeanProofs.IPRA.Analysis.FiniteCalculus
