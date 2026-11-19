import IPRADerivations.Core.Division
import IPRADerivations.Topology.StaggeredCells
import IPRADerivations.Foundations.TermSums
import IPRADerivations.Foundations.BoundedDecision

/-!
# Staggered grids and the injection count in every dimension (`dimension_invariance_ipra`)

Packet: `topology/dimension_invariance_ipra`, Section "Staggered rational cells and the
dimension obstruction", `lem:cells` and "A full simplex forces separated thresholds", for every
`d = d' + 1`. Values are natural numbers in units of `h/d` (as in `Topology/DimensionTwo` for
`d = 2`, where the unit is `h/2`); grid `g < d` has the cells `⌊(y + g)/d⌋` (`cell d' g y`), so the
boundaries of distinct grids are distinct residues modulo `d` (`eq:latticegap`).

* `two_boundaries`: two distinct grids `g < g' < d` do not both have a boundary between `x` and
  `x + 1`;
* `staggered_grid`: for three samples pairwise within `1` (the small-simplex condition in these
  units), `u, w` share a cell of grid `g` or `v, w` share a cell of grid `g'`: one target
  coordinate cannot separate two source directions;
* `cell_ne_of_gap`: samples at least `d` apart (separation by `h`) lie in different cells of every
  grid (`lem:cells` (i));
* `injection_absurd` (in Lean, for all `d`, `m`): `0/1` values `D c j` (`c < d`, `j < m`) with a
  `1` in every row and at most one `1` in every column exist only if `d ≤ m`; `pigeon`: its iPRA
  form, by `Foundations/BoundedDecision` (the packet's finite pigeonhole step).
-/

namespace LeanProofs.IPRA.Topology.StaggeredGrids

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm BigOperators
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)
open LeanProofs.IPRA.Topology.StaggeredCells (near near_cases dist)
open LeanProofs.IPRA.Foundations.TermSums

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The cell of `y` in grid `g` of mesh `d = d' + 1`: `⌊(y + g)/d⌋`. -/
abbrev cell (d' g : ℕ) (y : PTm n) : PTm n := quo (y + num g) (succ (num d'))

theorem eqb01' (a b : PTm n) : Γ ⊢[PRAAx] (eqb a b ≐ zero) ⋎ (eqb a b ≐ one) :=
  .orE (eq_or_ne a b) (.orI₂ (eqb_of_eq Prf.hyp0)) (.orI₁ (eqb_of_ne Prf.hyp0))

theorem eq_of_eqb {a b : PTm n} (h : Γ ⊢[PRAAx] eqb a b ≐ one) : Γ ⊢[PRAAx] a ≐ b :=
  .orE (eq_or_ne a b) Prf.hyp0 (.botE _ (succ_ne_zero (h.wk.eqSymm.eqTrans (eqb_of_ne Prf.hyp0))))

theorem congrEqb' {a a' b b' : PTm n} (h₁ : Γ ⊢[PRAAx] a ≐ a') (h₂ : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] eqb a b ≐ eqb a' b' :=
  congrMonus (.eqRefl _) (congrAdd (congrMonus h₁ h₂) (congrMonus h₂ h₁))

/-- A closed numeral comparison. -/
theorem num_lt {a b : ℕ} (h : a < b) : Γ ⊢[PRAAx] lt (num a) (num b) := by
  have e := Foundations.BoundedDecision.bounded_decide 0 (monus (succ (num a)) (num b) : PTm 0) zero
    (fun ρ _ => by simp; omega) (Fin.elim0 : Fin 0 → PTm n) (fun s => s.elim0) (Γ := Γ)
  simpa [lt, le] using e

/-- A closed numeral inequality as an `eqb`. -/
theorem eqb_num_ne {a b : ℕ} (h : a ≠ b) : Γ ⊢[PRAAx] eqb (num a) (num b) ≐ zero := by
  have e := Foundations.BoundedDecision.bounded_decide 0 (eqb (num a) (num b) : PTm 0) zero
    (fun ρ _ => by simp [h]) (Fin.elim0 : Fin 0 → PTm n) (fun s => s.elim0) (Γ := Γ)
  simpa using e

theorem congrQuo {a a' K : PTm n} (h : Γ ⊢[PRAAx] a ≐ a') : Γ ⊢[PRAAx] quo a K ≐ quo a' K :=
  congrAp2 _ h (.eqRefl _)

/-- Two distinct grids do not both have a boundary between `x` and `x + 1`. -/
theorem two_boundaries (d' g g' : ℕ) (hgg : g < g') (hg' : g' < d' + 1) (x : PTm n) :
    Γ ⊢[PRAAx] (cell d' g (succ x) ≐ cell d' g x) ⋎ (cell d' g' (succ x) ≐ cell d' g' x) := by
  obtain ⟨δ, rfl⟩ := Nat.exists_eq_add_of_lt hgg
  have hs : ∀ (k : ℕ) (Δ : List (Fm PTm n)), Δ ⊢[PRAAx] succ x + num k ≐ succ (x + num k) := fun k Δ => by
    apply deriveNat; ipra_simps; ring
  refine .orE (eqb01' (succ (rem (x + num g) (succ (num d')))) (succ (num d'))) ?_ ?_
  · -- no boundary of grid `g` between `x` and `x + 1`
    refine .orI₁ ?_
    exact (congrQuo (hs g _)).eqTrans ((quo_succ _ _).eqTrans
      ((congrAdd (.eqRefl _) Prf.hyp0).eqTrans (add_zero _)))
  · -- a boundary of grid `g`: then `x + g ≡ d − 1 (mod d)`, and grid `g'` has none
    refine .orI₂ ?_
    let Δ := (eqb (succ (rem (x + num g) (succ (num d')))) (succ (num d')) ≐ one) :: Γ
    have hr : Δ ⊢[PRAAx] rem (x + num g) (succ (num d')) ≐ num d' := succ_inj (eq_of_eqb Prf.hyp0)
    have hdm := div_mod (Γ := Δ) (x + num g) (num d')
    have hz : Δ ⊢[PRAAx] x + num (g + δ + 1) ≐
        succ (num d') * (quo (x + num g) (succ (num d')) + one) + num δ := by
      have e₁ := natEq (Prf.andE₁ hdm)
      have e₂ := natEq hr
      apply deriveNat; ipra_simps
      push_cast at e₁ e₂ ⊢
      linear_combination e₁ + e₂
    have hu := div_mod_unique hz (num_lt (a := δ) (b := d' + 1) (by omega))
    have hr' : Δ ⊢[PRAAx] eqb (succ (rem (x + num (g + δ + 1)) (succ (num d')))) (succ (num d')) ≐ zero :=
      (congrEqb' (congrSucc (Prf.andE₂ hu)) (.eqRefl _)).eqTrans
        (eqb_num_ne (a := δ + 1) (b := d' + 1) (by omega))
    exact (congrQuo (hs _ _)).eqTrans ((quo_succ _ _).eqTrans
      ((congrAdd (.eqRefl _) hr').eqTrans (add_zero _)))

private theorem two_step_absurd {a c : PTm n} (φ : Fm PTm n) (h₁ : Γ ⊢[PRAAx] c ≐ succ (succ a))
    (h₂ : Γ ⊢[PRAAx] le c (succ a)) : Γ ⊢[PRAAx] φ :=
  not_succ_le_self (succ a) φ (le_congr h₁ (.eqRefl _) h₂)

section Grids

variable (d' g g' : ℕ) (hgg : g < g') (hg' : g' < d' + 1)
include hgg hg'

private theorem case_below_g {u v w : PTm n} (hw : Γ ⊢[PRAAx] w ≐ succ u) (hv : Γ ⊢[PRAAx] w ≐ succ v) :
    Γ ⊢[PRAAx] (cell d' g u ≐ cell d' g w) ⋎ (cell d' g' v ≐ cell d' g' w) := by
  have huv : Γ ⊢[PRAAx] v ≐ u := succ_inj (hv.eqSymm.eqTrans hw)
  refine .orE (two_boundaries d' g g' hgg hg' u) (.orI₁ ?_) (.orI₂ ?_)
  · exact ((congrQuo (congrAdd hw.wk (.eqRefl _))).eqTrans Prf.hyp0).eqSymm
  · exact (congrQuo (congrAdd huv.wk (.eqRefl _))).eqTrans
      (Prf.hyp0.eqSymm.eqTrans (congrQuo (congrAdd hw.wk.eqSymm (.eqRefl _))))

private theorem case_above_g {u v w : PTm n} (hu : Γ ⊢[PRAAx] u ≐ succ w) (hv : Γ ⊢[PRAAx] v ≐ succ w) :
    Γ ⊢[PRAAx] (cell d' g u ≐ cell d' g w) ⋎ (cell d' g' v ≐ cell d' g' w) := by
  refine .orE (two_boundaries d' g g' hgg hg' w) (.orI₁ ?_) (.orI₂ ?_)
  · exact (congrQuo (congrAdd hu.wk (.eqRefl _))).eqTrans Prf.hyp0
  · exact (congrQuo (congrAdd hv.wk (.eqRefl _))).eqTrans Prf.hyp0

/-- Three samples pairwise within `1`: `u, w` share a cell of grid `g`, or `v, w` share a cell of
grid `g'`. -/
theorem staggered_grid {u v w : PTm n} (huw : Γ ⊢[PRAAx] near u w) (hvw : Γ ⊢[PRAAx] near v w)
    (huv : Γ ⊢[PRAAx] near u v) :
    Γ ⊢[PRAAx] (cell d' g u ≐ cell d' g w) ⋎ (cell d' g' v ≐ cell d' g' w) := by
  refine .orE (near_cases huw) (.orI₁ (congrQuo (congrAdd Prf.hyp0 (.eqRefl _)))) (.orE Prf.hyp0 ?_ ?_)
  · refine .orE (near_cases hvw.wk.wk) (.orI₂ (congrQuo (congrAdd Prf.hyp0 (.eqRefl _))))
      (.orE Prf.hyp0 ?_ ?_)
    · exact case_below_g d' g g' hgg hg' hyp2 Prf.hyp0
    · exact two_step_absurd _ (Prf.hyp0.eqTrans (congrSucc hyp2)) (.andE₂ huv.wk.wk.wk.wk)
  · refine .orE (near_cases hvw.wk.wk) (.orI₂ (congrQuo (congrAdd Prf.hyp0 (.eqRefl _))))
      (.orE Prf.hyp0 ?_ ?_)
    · exact two_step_absurd _ (hyp2.eqTrans (congrSucc Prf.hyp0)) (.andE₁ huv.wk.wk.wk.wk)
    · exact case_above_g d' g g' hgg hg' hyp2 Prf.hyp0

end Grids

/-- Samples at least `d` apart (separation by `h`) lie in different cells of every grid. -/
theorem cell_ne_of_gap (d' g : ℕ) {a b : PTm n} (h : Γ ⊢[PRAAx] le (a + succ (num d')) b) :
    Γ ⊢[PRAAx] neg (cell d' g a ≐ cell d' g b) := by
  refine .impI ?_
  let Δ := (cell d' g a ≐ cell d' g b) :: Γ
  have da := div_mod (Γ := Δ) (a + num g) (num d')
  have db := div_mod (Γ := Δ) (b + num g) (num d')
  have hb : Δ ⊢[PRAAx] b ≐ (a + succ (num d')) + monus b (a + succ (num d')) := (eq_add_of_le h).wk
  -- `a + g = d q + r` with the quotient of `b + g`
  have da' : Δ ⊢[PRAAx] a + num g ≐
      succ (num d') * quo (b + num g) (succ (num d')) + rem (a + num g) (succ (num d')) :=
    (Prf.andE₁ da).eqTrans (congrAdd (congrMul (.eqRefl _) Prf.hyp0) (.eqRefl _))
  have e : Δ ⊢[PRAAx] succ (num d') * quo (b + num g) (succ (num d')) + rem (b + num g) (succ (num d')) ≐
      succ (num d') * quo (b + num g) (succ (num d')) +
        (succ (num d') + (rem (a + num g) (succ (num d')) + monus b (a + succ (num d')))) := by
    have e₁ := natEq da'; have e₂ := natEq (Prf.andE₁ db); have e₃ := natEq hb
    apply deriveNat; ipra_simps
    linear_combination -e₂ + e₁ + e₃
  have hle : Δ ⊢[PRAAx] le (succ (num d')) (rem (b + num g) (succ (num d'))) :=
    le_of_eq_add (add_left_cancel e)
  exact le_lt_absurd _ hle (Prf.andE₂ db)

/-! ## The injection count -/

/-- `0/1` values with a `1` in every row and at most one `1` in every column: `d ≤ m`. -/
theorem injection_absurd {d m : ℕ} (hdm : m < d) (D : Fin d → Fin m → ℕ)
    (hrow : ∀ c, ∃ j, D c j = 1) (hcol : ∀ j c c', c ≠ c' → D c j = 1 → D c' j = 1 → False) : False := by
  choose f hf using hrow
  have hinj : Function.Injective f := fun c c' hcc => by
    by_contra hne
    exact hcol (f c) c c' hne (hf c) (hcc ▸ hf c')
  have := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at this
  omega

variable (d m : ℕ)

/-- The variable for the pair `(c, j)`. -/
def ix (c : Fin d) (j : Fin m) : Fin (d * m) := finProdFinEquiv (c, j)

/-- `[row c has a 1]`. -/
def rowPat (c : Fin d) : PTm (d * m) :=
  monus one (fprod m (fun j => monus one (Syn.var (ix d m c j))))

/-- `[no column has two 1s]`, the factor for the column `j` and the rows `c < c'`. -/
def colFac (j : Fin m) (c c' : Fin d) : PTm (d * m) :=
  if c < c' then monus one (Syn.var (ix d m c j) * Syn.var (ix d m c' j)) else one

/-- `[every row has a 1 and no column two]`. -/
def injPat : PTm (d * m) :=
  fprod d (rowPat d m) * fprod m (fun j => fprod d (fun c => fprod d (fun c' => colFac d m j c c')))

variable {d m}

theorem ev_injPat_zero (hdm : m < d) (ρ : Fin (d * m) → ℕ) (h01 : ∀ i, ρ i ≤ 1) :
    PTm.ev ρ (injPat d m) = 0 := by
  by_contra hne
  have hcf : ∀ j c c', PTm.ev ρ (colFac d m j c c') ≠ 0 := by
    intro j c c' h0
    apply hne
    simp only [injPat, ev_mul, ev_fprod]
    rw [Finset.prod_eq_zero (Finset.mem_univ j)
      (Finset.prod_eq_zero (Finset.mem_univ c) (Finset.prod_eq_zero (Finset.mem_univ c') h0)), MulZeroClass.mul_zero]
  have hrf : ∀ c, PTm.ev ρ (rowPat d m c) ≠ 0 := by
    intro c h0
    apply hne
    simp only [injPat, ev_mul, ev_fprod]
    rw [Finset.prod_eq_zero (Finset.mem_univ c) h0, MulZeroClass.zero_mul]
  refine injection_absurd hdm (fun c j => ρ (ix d m c j)) (fun c => ?_) (fun j c c' hcc h₁ h₂ => ?_)
  · have h := hrf c
    simp only [rowPat, ev_monus, ev_fprod, ev_var, ev_succ, ev_zero, Nat.zero_add] at h
    have hp : ∏ j : Fin m, (1 - ρ (ix d m c j)) = 0 := by omega
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hp
    exact ⟨j, by have := h01 (ix d m c j); omega⟩
  · rcases lt_or_gt_of_ne hcc with hlt | hlt
    · have h := hcf j c c'
      simp only [colFac, if_pos hlt, ev_monus, ev_mul, ev_var, ev_succ, ev_zero, h₁, h₂] at h
      exact h (by norm_num)
    · have h := hcf j c' c
      simp only [colFac, if_pos hlt, ev_monus, ev_mul, ev_var, ev_succ, ev_zero, h₁, h₂] at h
      exact h (by norm_num)

theorem fprod_one {k : ℕ} {f : Fin k → PTm n} (h : ∀ i, Γ ⊢[PRAAx] f i ≐ one) :
    Γ ⊢[PRAAx] fprod k f ≐ one := by
  apply of_mk
  rw [mk_fprod, Q.mk_one]
  exact Finset.prod_eq_one (fun i _ => by rw [Q.sound (h i), Q.mk_one])

theorem monus_one_zero {t : PTm n} (h : Γ ⊢[PRAAx] t ≐ zero) : Γ ⊢[PRAAx] monus one t ≐ one :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_zero _)

/-- The finite pigeonhole step: `0/1` terms `D c j` with a `1` in every row and no two `1`s in a
column are contradictory when `d > m`. -/
theorem pigeon (hdm : m < d) (D : Fin d → Fin m → PTm n) (h01 : ∀ c j, Γ ⊢[PRAAx] le (D c j) one)
    (hrow : ∀ c, Γ ⊢[PRAAx] fprod m (fun j => monus one (D c j)) ≐ zero)
    (hcol : ∀ j c c', c < c' → (Γ ⊢[PRAAx] D c j * D c' j ≐ zero)) : Γ ⊢[PRAAx] Fm.bot := by
  let σ : Fin (d * m) → PTm n := fun i => D (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  have hσ : ∀ c j, σ (ix d m c j) = D c j := fun c j => by simp only [σ, ix, Equiv.symm_apply_apply]
  have e₀ := Foundations.BoundedDecision.bounded_decide 1 (injPat d m) zero
    (fun ρ hρ => by rw [ev_injPat_zero hdm ρ hρ]; rfl) σ
    (fun i => h01 (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
  have e₁ : Γ ⊢[PRAAx] Syn.subst σ (injPat d m) ≐ one := by
    simp only [injPat, rowPat, colFac, PTm.subst_mul, subst_fprod, PTm.subst_monus, Syn.subst_var,
      hσ, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, apply_ite (Syn.subst σ)]
    refine (congrMul (fprod_one (fun c => monus_one_zero (hrow c)))
      (fprod_one (fun j => fprod_one (fun c => fprod_one (fun c' => ?_))))).eqTrans (one_mul _)
    split_ifs with hlt
    · exact monus_one_zero (hcol j c c' hlt)
    · exact .eqRefl _
  exact succ_ne_zero (e₁.eqSymm.eqTrans (by simpa using e₀))

end LeanProofs.IPRA.Topology.StaggeredGrids
