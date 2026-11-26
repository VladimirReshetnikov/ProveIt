import IPRADerivations.Analysis.FiniteOperations.FiniteCalculus
import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.Fubini
import IPRADerivations.Core.OrderCertificates

/-!
# The refinement estimate for Riemann sums

Packets: `analysis/calculus_ipra` (`report.tex`, Section `sec:integral`, "The finite refinement estimate",
`eq:refine`), `analysis/stirling_ipra` (`stirling_ipra.tex`, `eq:refine`) and `analysis/taylor_cauchy_ipra`
(Section `sec:integration`): if a sampled function has Lipschitz constant `B` on an interval of length `d`,
its left sum on `N` cells and the left sum on the refinement into `N r` cells differ by at most
`B d²/(2N)`. This is what makes the sequence of Riemann sums a regular name, i.e. the construction of the
integral.

For samples `f(i, x)` on the fine grid `i ≤ N r` and a bound `D` on the increments between neighbours:

* `refine_upper`: if `f(j + 1) ≤ f(j) + D` for `j < N r`, then
  `2 ∑_{i < N r} f(i) + D N r ≤ 2 r ∑_{k<N} f(k r) + D N r²`;
* `refine_lower`: if `f(j) ≤ f(j + 1) + D` for `j < N r`, then
  `2 r ∑_{k<N} f(k r) + D N r ≤ 2 ∑_{i < N r} f(i) + D N r²`.

Together: the fine sum and `r` times the coarse sum differ by at most `D N r (r − 1)/2`. With mesh
`h/r = d/(N r)` and `D = B h/r` this is `|S_N − S_{N r}| ≤ B d² (r − 1)/(2 N r) ≤ B d²/(2N)`.

The proof is an induction on the number of coarse cells; each cell is `cell_upper`/`cell_lower` of
`Analysis/FiniteCalculus` for the offset body. The hypothesis is the formula `StepUp f x B D`
(`StepDn`), which commutes with substitution (`shift_StepUp`), so it is available unchanged under the
binders of the induction and of the cell (`step_off`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RiemannRefinement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.FiniteCalculus (cell_upper cell_lower)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Increment hypotheses as formulas -/

/-- `f(j + 1, x) ≤ f(j, x) + D` for `j < B`. -/
def StepUp (f : PTm 2) (x B D : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift B) ⟶
    le (inst2 f (succ (var 0)) (Syn.shift x)) (inst2 f (var 0) (Syn.shift x) + Syn.shift D))

/-- `f(j, x) ≤ f(j + 1, x) + D` for `j < B`. -/
def StepDn (f : PTm 2) (x B D : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift B) ⟶
    le (inst2 f (var 0) (Syn.shift x)) (inst2 f (succ (var 0)) (Syn.shift x) + Syn.shift D))

theorem subst_StepUp {m : ℕ} (σ : Fin n → PTm m) (f : PTm 2) (x B D : PTm n) :
    (StepUp f x B D).subst σ = StepUp f (Syn.subst σ x) (Syn.subst σ B) (Syn.subst σ D) := by
  simp only [StepUp, Fm.subst_all, Fm.subst_imp, subst_lt, subst_le, subst_inst2, PTm.subst_add,
    Syn.subst_var, Syn.up_zero, Syn.subst_shift, Syn.shift_subst, Syn.up_succ, ConciseIPRA.PTm.subst_succ]

theorem subst_StepDn {m : ℕ} (σ : Fin n → PTm m) (f : PTm 2) (x B D : PTm n) :
    (StepDn f x B D).subst σ = StepDn f (Syn.subst σ x) (Syn.subst σ B) (Syn.subst σ D) := by
  simp only [StepDn, Fm.subst_all, Fm.subst_imp, subst_lt, subst_le, subst_inst2, PTm.subst_add,
    Syn.subst_var, Syn.up_zero, Syn.subst_shift, Syn.shift_subst, Syn.up_succ, ConciseIPRA.PTm.subst_succ]

theorem shift_StepUp (f : PTm 2) (x B D : PTm n) :
    Fm.shift (StepUp f x B D) = StepUp f (Syn.shift x) (Syn.shift B) (Syn.shift D) := subst_StepUp _ _ _ _ _

theorem shift_StepDn (f : PTm 2) (x B D : PTm n) :
    Fm.shift (StepDn f x B D) = StepDn f (Syn.shift x) (Syn.shift B) (Syn.shift D) := subst_StepDn _ _ _ _ _

/-- The hypothesis at a given index. -/
theorem up_at {f : PTm 2} {x B D t : PTm n} (h : Γ ⊢[PRAAx] StepUp f x B D) (ht : Γ ⊢[PRAAx] lt t B) :
    Γ ⊢[PRAAx] le (inst2 f (succ t) x) (inst2 f t x + D) := by
  have a := Prf.allE t h
  simp only [Fm.subst_imp, subst_lt, subst_le, subst_inst2, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ] at a
  exact Prf.impE a ht

theorem dn_at {f : PTm 2} {x B D t : PTm n} (h : Γ ⊢[PRAAx] StepDn f x B D) (ht : Γ ⊢[PRAAx] lt t B) :
    Γ ⊢[PRAAx] le (inst2 f t x) (inst2 f (succ t) x + D) := by
  have a := Prf.allE t h
  simp only [Fm.subst_imp, subst_lt, subst_le, subst_inst2, PTm.subst_add, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ] at a
  exact Prf.impE a ht

theorem shift_le' {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) := by
  have e := h.shift
  simp only [Fm.shift, subst_le] at e
  exact e

/-- The offset index of a cell: `(A + (j + 1), A + j)` read through the pair `⟨A, x⟩`. -/
theorem off_succ (A x j : PTm n) : Γ ⊢[PRAAx] succ (A + j) ≐ fstT (pairT A x) + succ j :=
  ((congrAdd (fst_pair A x) (.eqRefl (succ j))).eqTrans
    (by ipra_ring : Γ ⊢[PRAAx] A + succ j ≐ succ (A + j))).eqSymm

theorem off_same (A x j : PTm n) : Γ ⊢[PRAAx] A + j ≐ fstT (pairT A x) + j :=
  (congrAdd (fst_pair A x) (.eqRefl j)).eqSymm

/-- The hypothesis on `[0, B)` gives the hypothesis for the cell `[A, A + r)`. -/
theorem up_off {f : PTm 2} {x B D A r : PTm n} (h : Γ ⊢[PRAAx] StepUp f x B D)
    (hA : Γ ⊢[PRAAx] le (A + r) B) : Γ ⊢[PRAAx] StepUp (offB f) (pairT A x) r D := by
  refine .allI (.impI ?_)
  have h' : (lt (var 0) (Syn.shift r) :: Γ.map Fm.shift) ⊢[PRAAx]
      StepUp f (Syn.shift x) (Syn.shift B) (Syn.shift D) := by
    have a := h.shift
    rw [shift_StepUp] at a
    exact a.wk
  have hA' := (shift_le' hA).wk (ψ := lt (var 0) (Syn.shift r))
  have eA : Syn.shift (A + r) = Syn.shift A + Syn.shift r := by simp [Syn.shift]
  rw [eA] at hA'
  have hj : (lt (var 0) (Syn.shift r) :: Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (Syn.shift r) := Prf.hyp0
  have ht : (lt (var 0) (Syn.shift r) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (succ (Syn.shift A + var 0)) (Syn.shift B) := by
    ipra_le sl hA' + sl hj
  have s := up_at h' ht
  rw [shift_pairT, inst2_offB, inst2_offB]
  exact le_congr (congrInst2 f (off_succ _ _ _) (snd_pair _ _).eqSymm)
    (congrAdd (congrInst2 f (off_same _ _ _) (snd_pair _ _).eqSymm) (.eqRefl _)) s

theorem dn_off {f : PTm 2} {x B D A r : PTm n} (h : Γ ⊢[PRAAx] StepDn f x B D)
    (hA : Γ ⊢[PRAAx] le (A + r) B) : Γ ⊢[PRAAx] StepDn (offB f) (pairT A x) r D := by
  refine .allI (.impI ?_)
  have h' : (lt (var 0) (Syn.shift r) :: Γ.map Fm.shift) ⊢[PRAAx]
      StepDn f (Syn.shift x) (Syn.shift B) (Syn.shift D) := by
    have a := h.shift
    rw [shift_StepDn] at a
    exact a.wk
  have hA' := (shift_le' hA).wk (ψ := lt (var 0) (Syn.shift r))
  have eA : Syn.shift (A + r) = Syn.shift A + Syn.shift r := by simp [Syn.shift]
  rw [eA] at hA'
  have hj : (lt (var 0) (Syn.shift r) :: Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (Syn.shift r) := Prf.hyp0
  have ht : (lt (var 0) (Syn.shift r) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (succ (Syn.shift A + var 0)) (Syn.shift B) := by
    ipra_le sl hA' + sl hj
  have s := dn_at h' ht
  rw [shift_pairT, inst2_offB, inst2_offB]
  exact le_congr (congrInst2 f (off_same _ _ _) (snd_pair _ _).eqSymm)
    (congrAdd (congrInst2 f (off_succ _ _ _) (snd_pair _ _).eqSymm) (.eqRefl _)) s

/-! ## The coarse samples -/

/-- `f(k r, x)` over `0 = k`, `1 = ⟨r, x⟩`. -/
def crsB (f : PTm 2) : PTm 2 := Syn.subst ![var 0 * fstT (var 1), sndT (var 1)] f

theorem inst2_crsB (f : PTm 2) (k y : PTm n) :
    inst2 (crsB f) k y = inst2 f (k * fstT y) (sndT y) := by
  simp only [inst2, crsB, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

theorem crs_at (f : PTm 2) (k r x : PTm n) :
    Γ ⊢[PRAAx] inst2 (crsB f) k (pairT r x) ≐ inst2 f (k * r) x := by
  rw [inst2_crsB]
  exact congrInst2 f (congrMul (.eqRefl _) (fst_pair _ _)) (snd_pair _ _)

/-- The first sample of the cell at `A`. -/
theorem off_zero (f : PTm 2) (A x : PTm n) : Γ ⊢[PRAAx] inst2 (offB f) zero (pairT A x) ≐ inst2 f A x := by
  rw [inst2_offB]
  exact congrInst2 f ((congrAdd (fst_pair _ _) (.eqRefl _)).eqTrans (add_zero _)) (snd_pair _ _)

/-- The fine sum over one more cell. -/
theorem fine_succ (f : PTm 2) (k r x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF f) (succ k * r) x ≐
      ap2 (sumF f) (k * r) x + ap2 (sumF (offB f)) r (pairT (k * r) x) :=
  (congrAp2 (sumF f) (by ipra_ring : Γ ⊢[PRAAx] succ k * r ≐ k * r + r)
    (.eqRefl x)).eqTrans (sum_split f (k * r) r x)

theorem fine_zero (f : PTm 2) (r x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF f) (zero * r) x ≐ zero :=
  (congrAp2 (sumF f) (zero_mul r) (.eqRefl x)).eqTrans (sum_zero f x)

/-! ## The refinement estimate -/

/-- `2 ∑_{i < k r} f(i) + D k r ≤ 2 r ∑_{k'<k} f(k' r) + D k r²`. -/
abbrev RefUp (f : PTm 2) (k r x D : PTm n) : Fm PTm n :=
  le (two * ap2 (sumF f) (k * r) x + D * (k * r))
    (two * (r * ap2 (sumF (crsB f)) k (pairT r x)) + D * (k * (r * r)))

/-- `2 r ∑_{k'<k} f(k' r) + D k r ≤ 2 ∑_{i < k r} f(i) + D k r²`. -/
abbrev RefDn (f : PTm 2) (k r x D : PTm n) : Fm PTm n :=
  le (two * (r * ap2 (sumF (crsB f)) k (pairT r x)) + D * (k * r))
    (two * ap2 (sumF f) (k * r) x + D * (k * (r * r)))

theorem refUp_base (f : PTm 2) (r x D : PTm n) : Γ ⊢[PRAAx] RefUp f zero r x D := by
  have z1 := natEq (fine_zero (Γ := Γ) f r x)
  have z2 := natEq (sum_zero (Γ := Γ) (crsB f) (pairT r x))
  ipra_le 0 using rw [z1, z2]; ring

theorem refDn_base (f : PTm 2) (r x D : PTm n) : Γ ⊢[PRAAx] RefDn f zero r x D := by
  have z1 := natEq (fine_zero (Γ := Γ) f r x)
  have z2 := natEq (sum_zero (Γ := Γ) (crsB f) (pairT r x))
  ipra_le 0 using rw [z1, z2]; ring

theorem refUp_step {f : PTm 2} {k r x D : PTm n}
    (c : Γ ⊢[PRAAx] le (two * ap2 (sumF (offB f)) r (pairT (k * r) x) + D * r)
      (two * (r * inst2 (offB f) zero (pairT (k * r) x)) + D * (r * r)))
    (ih : Γ ⊢[PRAAx] RefUp f k r x D) : Γ ⊢[PRAAx] RefUp f (succ k) r x D := by
  have eS := natEq (fine_succ (Γ := Γ) f k r x)
  have eC := natEq (sum_succ' (Γ := Γ) (crsB f) k (pairT r x))
  have eA := natEq (crs_at (Γ := Γ) f k r x)
  have eO := natEq (off_zero (Γ := Γ) f (k * r) x)
  ipra_le sl ih + sl c using rw [eS, eC, eA, eO]; ring

theorem refDn_step {f : PTm 2} {k r x D : PTm n}
    (c : Γ ⊢[PRAAx] le (two * (r * inst2 (offB f) zero (pairT (k * r) x)) + D * r)
      (two * ap2 (sumF (offB f)) r (pairT (k * r) x) + D * (r * r)))
    (ih : Γ ⊢[PRAAx] RefDn f k r x D) : Γ ⊢[PRAAx] RefDn f (succ k) r x D := by
  have eS := natEq (fine_succ (Γ := Γ) f k r x)
  have eC := natEq (sum_succ' (Γ := Γ) (crsB f) k (pairT r x))
  have eA := natEq (crs_at (Γ := Γ) f k r x)
  have eO := natEq (off_zero (Γ := Γ) f (k * r) x)
  ipra_le sl ih + sl c using rw [eS, eC, eA, eO]; ring

/-- `eq:refine`, upper half: if `f(j + 1) ≤ f(j) + D` for `j < N r`, then
`2 ∑_{i < N r} f(i) + D N r ≤ 2 r ∑_{k<N} f(k r) + D N r²`. -/
theorem refine_upper (f : PTm 2) (x N r D : PTm n) (h : Γ ⊢[PRAAx] StepUp f x (N * r) D) :
    Γ ⊢[PRAAx] RefUp f N r x D := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      RefUp f (var 0) (Syn.shift r) (Syn.shift x) (Syn.shift D)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact .impI (refUp_base f r x D)
    · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      have hk : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶ RefUp f (var 0) (Syn.shift r) (Syn.shift x) (Syn.shift D)) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (Syn.shift N) := Prf.hyp0
      have ih := Prf.impE Prf.hyp1 (le_trans (le_succ_self _) hk)
      have h' : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶ RefUp f (var 0) (Syn.shift r) (Syn.shift x) (Syn.shift D)) ::
          Γ.map Fm.shift) ⊢[PRAAx] StepUp f (Syn.shift x) (Syn.shift N * Syn.shift r) (Syn.shift D) := by
        have a := h.shift
        have e : Syn.shift (N * r) = Syn.shift N * Syn.shift r := by simp [Syn.shift]
        rw [shift_StepUp, e] at a
        exact a.wk.wk
      have hA : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶ RefUp f (var 0) (Syn.shift r) (Syn.shift x) (Syn.shift D)) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (var 0 * Syn.shift r + Syn.shift r) (Syn.shift N * Syn.shift r) := by
        ipra_le sl hk * 𝔟 (Syn.shift r)
      exact refUp_step (cell_upper (offB f) (pairT (var 0 * Syn.shift r) (Syn.shift x)) (Syn.shift r)
        (Syn.shift D) (up_off h' hA)) ih
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h2
  exact .impE h2 (le_refl N)

/-- `eq:refine`, lower half: if `f(j) ≤ f(j + 1) + D` for `j < N r`, then
`2 r ∑_{k<N} f(k r) + D N r ≤ 2 ∑_{i < N r} f(i) + D N r²`. -/
theorem refine_lower (f : PTm 2) (x N r D : PTm n) (h : Γ ⊢[PRAAx] StepDn f x (N * r) D) :
    Γ ⊢[PRAAx] RefDn f N r x D := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      RefDn f (var 0) (Syn.shift r) (Syn.shift x) (Syn.shift D)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      exact .impI (refDn_base f r x D)
    · simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      refine .impI ?_
      have hk : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶ RefDn f (var 0) (Syn.shift r) (Syn.shift x) (Syn.shift D)) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (Syn.shift N) := Prf.hyp0
      have ih := Prf.impE Prf.hyp1 (le_trans (le_succ_self _) hk)
      have h' : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶ RefDn f (var 0) (Syn.shift r) (Syn.shift x) (Syn.shift D)) ::
          Γ.map Fm.shift) ⊢[PRAAx] StepDn f (Syn.shift x) (Syn.shift N * Syn.shift r) (Syn.shift D) := by
        have a := h.shift
        have e : Syn.shift (N * r) = Syn.shift N * Syn.shift r := by simp [Syn.shift]
        rw [shift_StepDn, e] at a
        exact a.wk.wk
      have hA : (le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶ RefDn f (var 0) (Syn.shift r) (Syn.shift x) (Syn.shift D)) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (var 0 * Syn.shift r + Syn.shift r) (Syn.shift N * Syn.shift r) := by
        ipra_le sl hk * 𝔟 (Syn.shift r)
      exact refDn_step (cell_lower (offB f) (pairT (var 0 * Syn.shift r) (Syn.shift x)) (Syn.shift r)
        (Syn.shift D) (dn_off h' hA)) ih
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at h2
  exact .impE h2 (le_refl N)

end LeanProofs.IPRA.Analysis.RiemannRefinement
