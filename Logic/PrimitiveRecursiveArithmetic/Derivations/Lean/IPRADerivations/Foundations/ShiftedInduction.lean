import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Probability.PoissonShift
import IPRADerivations.Core.BoundedSums

/-!
# Induction with a shifting parameter

A reusable principle of the embedding framework (`foundations/ipra_framework`, the discipline of
quantifier-free induction; used for `analysis/hypergeometric_ipra_2026-11-16`, Theorem `thm:vandermonde`,
whose proof is an induction on `m` "uniformly in `b, c`" with the step
`S_{m+1}(b, c) = S_m(b, c) − (b/c) S_m(b + 1, c + 1)`).

For an equation `L(m, b, x) = R(m, b, x)` between terms: if

* `L(0, b, x) = R(0, b, x)` for all `b`, `x`, and
* `L(m, b, x) = R(m, b, x)` and `L(m, b + 1, x) = R(m, b + 1, x)` give
  `L(m + 1, b, x) = R(m + 1, b, x)`,

then `L(m, b, x) = R(m, b, x)` for all `m`, `b`, `x` (`shifted_induction`). The step uses the hypothesis
at a different parameter, so the induction formula would need `∀ b`. It is replaced by a bounded
universal: to reach level `M` at `b` one needs level `m ≤ M` only at the parameters `b + j`,
`j ≤ M − m`. The bounded universal is the primitive-recursive bit `allB` of
`Foundations/BoundedReflection`, and the induction is on the quantifier-free equation

`allB_{j ≤ M ∸ m} [L(m, b + j, x) = R(m, b + j, x)] = 1`.

* `shB L R`: the bit `[L(m, b + j, x) = R(m, b + j, x)]` as a body in `j` with the parameter
  `⟨m, ⟨b, x⟩⟩`; `sh_intro`, `sh_elim`: its meaning;
* `sh_base`, `sh_pt`, `sh_step`, `sh_all`: the induction;
* `shifted_induction`: the principle.

The base and the step are given as derivations of open formulas in the empty context (variables
`0 = b`, `1 = x`, respectively `0 = m`, `1 = b`, `2 = x`), which are instantiated at arbitrary terms;
further parameters are carried inside `x`.
-/

namespace LeanProofs.IPRA.Foundations.ShiftedInduction

open_ipra exports
open LeanProofs.IPRA.Foundations.BoundedReflection (allB all_elim all_intro one_ne_zero)
open LeanProofs.IPRA.Probability.PoissonShift (monus_pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

section Shifted

variable (L R : PTm 3)

/-- The bit `[L(m, b + j, x) = R(m, b + j, x)]`; variables `0 = j`, `1 = y = ⟨m, ⟨b, x⟩⟩`. -/
def shB : PTm 2 :=
  eqb (inst3 L (fstT (var 1)) (fstT (sndT (var 1)) + var 0) (sndT (sndT (var 1))))
    (inst3 R (fstT (var 1)) (fstT (sndT (var 1)) + var 0) (sndT (sndT (var 1))))

theorem inst2_shB (j y : PTm n) :
    inst2 (shB L R) j y =
      eqb (inst3 L (fstT y) (fstT (sndT y) + j) (sndT (sndT y)))
        (inst3 R (fstT y) (fstT (sndT y) + j) (sndT (sndT y))) := by
  simp [inst2, shB]

/-- Reading a body at the parameter `⟨m, ⟨b, x⟩⟩`. -/
theorem read_at (g : PTm 3) (j m b x : PTm n) :
    Γ ⊢[PRAAx] inst3 g (fstT (pairT m (pairT b x))) (fstT (sndT (pairT m (pairT b x))) + j)
        (sndT (sndT (pairT m (pairT b x)))) ≐ inst3 g m (b + j) x :=
  congrInst3 g (fst_pair m _)
    (congrAdd ((congrFst (snd_pair m (pairT b x))).eqTrans (fst_pair b x)) (.eqRefl j))
    ((congrSnd (snd_pair m (pairT b x))).eqTrans (snd_pair b x))

theorem sh_intro {j m b x : PTm n} (h : Γ ⊢[PRAAx] inst3 L m (b + j) x ≐ inst3 R m (b + j) x) :
    Γ ⊢[PRAAx] neg (inst2 (shB L R) j (pairT m (pairT b x)) ≐ zero) := by
  rw [inst2_shB]
  have e := ((read_at (Γ := Γ) L j m b x).eqTrans h).eqTrans (read_at (Γ := Γ) R j m b x).eqSymm
  exact .impI (one_ne_zero _ ((eqb_of_eq e.wk).eqSymm.eqTrans Prf.hyp0))

theorem sh_elim {j m b x : PTm n}
    (h : Γ ⊢[PRAAx] neg (inst2 (shB L R) j (pairT m (pairT b x)) ≐ zero)) :
    Γ ⊢[PRAAx] inst3 L m (b + j) x ≐ inst3 R m (b + j) x := by
  rw [inst2_shB] at h
  exact ((read_at (Γ := Γ) L j m b x).eqSymm.eqTrans (eq_of_eqb_ne h)).eqTrans (read_at (Γ := Γ) R j m b x)

variable {L R}

/-- The base instantiated at arbitrary terms. -/
theorem base_at
    (hbase : ([] : List (Fm PTm 2)) ⊢[PRAAx] inst3 L zero (var 0) (var 1) ≐ inst3 R zero (var 0) (var 1))
    (b x : PTm n) : Γ ⊢[PRAAx] inst3 L zero b x ≐ inst3 R zero b x := by
  have h := inst (Γ := Γ) hbase (![b, x] : Fin 2 → PTm n)
  simpa using h

/-- The step instantiated at arbitrary terms. -/
theorem step_at
    (hstep : ([] : List (Fm PTm 3)) ⊢[PRAAx]
      (inst3 L (var 0) (var 1) (var 2) ≐ inst3 R (var 0) (var 1) (var 2)) ⟶
      ((inst3 L (var 0) (succ (var 1)) (var 2) ≐ inst3 R (var 0) (succ (var 1)) (var 2)) ⟶
        (inst3 L (succ (var 0)) (var 1) (var 2) ≐ inst3 R (succ (var 0)) (var 1) (var 2))))
    {m b x : PTm n} (h₀ : Γ ⊢[PRAAx] inst3 L m b x ≐ inst3 R m b x)
    (h₁ : Γ ⊢[PRAAx] inst3 L m (succ b) x ≐ inst3 R m (succ b) x) :
    Γ ⊢[PRAAx] inst3 L (succ m) b x ≐ inst3 R (succ m) b x := by
  have h := inst (Γ := Γ) hstep (![m, b, x] : Fin 3 → PTm n)
  simp only [Fm.subst_imp, Fm.subst_eq, subst_inst3, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    ConciseIPRA.PTm.subst_succ] at h
  exact Prf.impE (Prf.impE h h₀) h₁

/-- Level `0` holds at all parameters `b + j`. -/
theorem sh_base
    (hbase : ([] : List (Fm PTm 2)) ⊢[PRAAx] inst3 L zero (var 0) (var 1) ≐ inst3 R zero (var 0) (var 1))
    (N b x : PTm n) : Γ ⊢[PRAAx] allB (shB L R) N (pairT zero (pairT b x)) ≐ one := by
  refine all_intro (shB L R) (.allI (.impI ?_))
  have e : Syn.shift (pairT zero (pairT b x)) = pairT zero (pairT (Syn.shift b) (Syn.shift x)) := by
    simp [Syn.shift]
  rw [e]
  exact sh_intro L R (base_at hbase _ _)

/-- One level up at the parameter `b + j`, for `j ≤ M − (m + 1)`. -/
theorem sh_pt
    (hstep : ([] : List (Fm PTm 3)) ⊢[PRAAx]
      (inst3 L (var 0) (var 1) (var 2) ≐ inst3 R (var 0) (var 1) (var 2)) ⟶
      ((inst3 L (var 0) (succ (var 1)) (var 2) ≐ inst3 R (var 0) (succ (var 1)) (var 2)) ⟶
        (inst3 L (succ (var 0)) (var 1) (var 2) ≐ inst3 R (succ (var 0)) (var 1) (var 2))))
    {j m M b x : PTm n} (hm : Γ ⊢[PRAAx] lt m M)
    (ih : Γ ⊢[PRAAx] allB (shB L R) (succ (monus M m)) (pairT m (pairT b x)) ≐ one)
    (hj : Γ ⊢[PRAAx] lt j (succ (monus M (succ m)))) :
    Γ ⊢[PRAAx] neg (inst2 (shB L R) j (pairT (succ m) (pairT b x)) ≐ zero) := by
  have mp := monus_pred hm
  have hj' : Γ ⊢[PRAAx] le (succ j) (succ (monus M (succ m))) := hj
  have h₀ : Γ ⊢[PRAAx] lt j (succ (monus M m)) :=
    lt_congr (.eqRefl j) (congrSucc mp).eqSymm (le_trans hj' (le_succ_self _))
  have h₁ : Γ ⊢[PRAAx] lt (succ j) (succ (monus M m)) :=
    lt_congr (.eqRefl (succ j)) (congrSucc mp).eqSymm ((succ_monus_succ _ _).eqTrans hj')
  have a₀ := sh_elim L R (all_elim (shB L R) ih h₀)
  have a₁ := sh_elim L R (all_elim (shB L R) ih h₁)
  have cL := congrInst3 L (.eqRefl m) (add_succ (Γ := Γ) b j) (.eqRefl x)
  have cR := congrInst3 R (.eqRefl m) (add_succ (Γ := Γ) b j) (.eqRefl x)
  exact sh_intro L R (step_at hstep a₀ ((cL.eqSymm.eqTrans a₁).eqTrans cR))

theorem sh_step
    (hstep : ([] : List (Fm PTm 3)) ⊢[PRAAx]
      (inst3 L (var 0) (var 1) (var 2) ≐ inst3 R (var 0) (var 1) (var 2)) ⟶
      ((inst3 L (var 0) (succ (var 1)) (var 2) ≐ inst3 R (var 0) (succ (var 1)) (var 2)) ⟶
        (inst3 L (succ (var 0)) (var 1) (var 2) ≐ inst3 R (succ (var 0)) (var 1) (var 2))))
    {m M b x : PTm n} (hm : Γ ⊢[PRAAx] lt m M)
    (ih : Γ ⊢[PRAAx] allB (shB L R) (succ (monus M m)) (pairT m (pairT b x)) ≐ one) :
    Γ ⊢[PRAAx] allB (shB L R) (succ (monus M (succ m))) (pairT (succ m) (pairT b x)) ≐ one := by
  refine all_intro (shB L R) (.allI (.impI ?_))
  have eY : Syn.shift (pairT (succ m) (pairT b x)) =
      pairT (succ (Syn.shift m)) (pairT (Syn.shift b) (Syn.shift x)) := by
    simp [Syn.shift]
  have eN : Syn.shift (succ (monus M (succ m))) = succ (monus (Syn.shift M) (succ (Syn.shift m))) := by
    simp [Syn.shift]
  rw [eY, eN]
  have hm' := hm.shift
  have e₁ : Fm.shift (lt m M) = lt (Syn.shift m) (Syn.shift M) := by simp [Fm.shift, Syn.shift]
  rw [e₁] at hm'
  have ih' := ih.shift
  have e₂ : Fm.shift (allB (shB L R) (succ (monus M m)) (pairT m (pairT b x)) ≐ one) =
      (allB (shB L R) (succ (monus (Syn.shift M) (Syn.shift m)))
        (pairT (Syn.shift m) (pairT (Syn.shift b) (Syn.shift x))) ≐ one) := by
    simp [Fm.shift, Syn.shift]
  rw [e₂] at ih'
  exact sh_pt hstep hm'.wk ih'.wk Prf.hyp0

theorem sh_guard
    (hstep : ([] : List (Fm PTm 3)) ⊢[PRAAx]
      (inst3 L (var 0) (var 1) (var 2) ≐ inst3 R (var 0) (var 1) (var 2)) ⟶
      ((inst3 L (var 0) (succ (var 1)) (var 2) ≐ inst3 R (var 0) (succ (var 1)) (var 2)) ⟶
        (inst3 L (succ (var 0)) (var 1) (var 2) ≐ inst3 R (succ (var 0)) (var 1) (var 2))))
    {m M b x : PTm n} (hm : Γ ⊢[PRAAx] le (succ m) M)
    (ih : Γ ⊢[PRAAx] le m M ⟶
      (allB (shB L R) (succ (monus M m)) (pairT m (pairT b x)) ≐ one)) :
    Γ ⊢[PRAAx] allB (shB L R) (succ (monus M (succ m))) (pairT (succ m) (pairT b x)) ≐ one :=
  sh_step hstep hm (Prf.impE ih (le_trans (le_succ_self m) hm))

theorem sh_all
    (hbase : ([] : List (Fm PTm 2)) ⊢[PRAAx] inst3 L zero (var 0) (var 1) ≐ inst3 R zero (var 0) (var 1))
    (hstep : ([] : List (Fm PTm 3)) ⊢[PRAAx]
      (inst3 L (var 0) (var 1) (var 2) ≐ inst3 R (var 0) (var 1) (var 2)) ⟶
      ((inst3 L (var 0) (succ (var 1)) (var 2) ≐ inst3 R (var 0) (succ (var 1)) (var 2)) ⟶
        (inst3 L (succ (var 0)) (var 1) (var 2) ≐ inst3 R (succ (var 0)) (var 1) (var 2))))
    (M b x : PTm n) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift M) ⟶
      (allB (shB L R) (succ (monus (Syn.shift M) (var 0)))
        (pairT (var 0) (pairT (Syn.shift b) (Syn.shift x))) ≐ one)) := by
  refine qfIndAllUpTo M trivial ?_ ?_
  · simpa using sh_base (Γ := Γ) hbase (succ (monus M zero)) b x
  · simp
    exact .impI (sh_step hstep Prf.hyp0 Prf.hyp1)

/-- Induction with a shifting parameter: the step may use the hypothesis at `b` and at `b + 1`. -/
theorem shifted_induction
    (hbase : ([] : List (Fm PTm 2)) ⊢[PRAAx] inst3 L zero (var 0) (var 1) ≐ inst3 R zero (var 0) (var 1))
    (hstep : ([] : List (Fm PTm 3)) ⊢[PRAAx]
      (inst3 L (var 0) (var 1) (var 2) ≐ inst3 R (var 0) (var 1) (var 2)) ⟶
      ((inst3 L (var 0) (succ (var 1)) (var 2) ≐ inst3 R (var 0) (succ (var 1)) (var 2)) ⟶
        (inst3 L (succ (var 0)) (var 1) (var 2) ≐ inst3 R (succ (var 0)) (var 1) (var 2))))
    (m b x : PTm n) : Γ ⊢[PRAAx] inst3 L m b x ≐ inst3 R m b x := by
  have a := Prf.allE m (sh_all (Γ := Γ) hbase hstep m b x)
  have e : (le (var 0) (Syn.shift m) ⟶
        (allB (shB L R) (succ (monus (Syn.shift m) (var 0)))
          (pairT (var 0) (pairT (Syn.shift b) (Syn.shift x))) ≐ one)).subst (Syn.inst m) =
      (le m m ⟶ (allB (shB L R) (succ (monus m m)) (pairT m (pairT b x)) ≐ one)) := by
    simp
  rw [e] at a
  have h := sh_elim L R (all_elim (shB L R) (Prf.impE a (le_refl m)) (zero_lt_succ _))
  exact ((congrInst3 L (.eqRefl m) (add_zero (Γ := Γ) b) (.eqRefl x)).eqSymm.eqTrans h).eqTrans
    (congrInst3 R (.eqRefl m) (add_zero (Γ := Γ) b) (.eqRefl x))

end Shifted

end LeanProofs.IPRA.Foundations.ShiftedInduction
