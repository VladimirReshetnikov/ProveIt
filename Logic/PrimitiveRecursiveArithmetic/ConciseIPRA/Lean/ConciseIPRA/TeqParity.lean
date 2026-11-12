import ConciseIPRA.TeqArith

/-!
# Parity, a residue cycle and the ramp in `T_eq`

`T_eq` has no predecessor symbol, so a comparison of two numbers has to be
obtained from iteration alone.  This module builds the arithmetic part of that
bootstrap:

* `zf n = sel n 1 0`, the zero test, and `par n = I(n, 0; u. zf u)`, the parity;
* `cyc`, which sends `0, 1, 2` to `1, 2, 0`, and `mod3 n = I(n, 0; u. cyc u)`;
* the ramp `ramp n = I(n, 0; u. S (u + mod3 u))`, with the invariant
  `mod3 (ramp n) = par n`, so that `ramp (2 n) = 3 n` and
  `ramp (3 n) = 3 ramp n + par n`;
* `hop u = sel (par u) (ramp u) u`, which replaces a factor two by a factor
  three and fixes the numbers of parity one:
  `hop (2 u) = 3 u`, `hop 1 = 1`, `hop (3 u) = 3 hop u`.

Here `2 u` and `3 u` abbreviate `u + u` and `u + u + u`.  A Boolean value is
split by `Q.par_cases`, which is coverage stated over all extensions of the
context.
-/

namespace LeanProofs.ConciseIPRA

open Syn
open scoped Fm

variable {n m : ℕ}

/-- The zero test: `1` at zero and `0` at a successor. -/
def Tm.zf (a : Tm n) : Tm n := Tm.sel a Tm.one Tm.zero

/-- The parity `I(a, 0; u. zf u)`. -/
def Tm.par (a : Tm n) : Tm n := Tm.iter a Tm.zero (Tm.zf (Syn.var 0))

/-- The cycle `0 ↦ 1 ↦ 2 ↦ 0`. -/
def Tm.cyc (a : Tm n) : Tm n := Tm.add (Tm.zf a) (Tm.add (Tm.par a) (Tm.par a))

/-- The iterated cycle `I(a, 0; u. cyc u)`. -/
def Tm.mod3 (a : Tm n) : Tm n := Tm.iter a Tm.zero (Tm.cyc (Syn.var 0))

/-- The ramp `I(a, 0; u. S (u + mod3 u))`. -/
def Tm.ramp (a : Tm n) : Tm n :=
  Tm.iter a Tm.zero (Tm.succ (Tm.add (Syn.var 0) (Tm.mod3 (Syn.var 0))))

/-- The factor map: the ramp at parity zero, the identity at parity one. -/
def Tm.hop (a : Tm n) : Tm n := Tm.sel (Tm.par a) (Tm.ramp a) a

@[simp] theorem Tm.subst_zf (σ : Fin n → Tm m) (a : Tm n) :
    Syn.subst σ (Tm.zf a) = Tm.zf (Syn.subst σ a) := by
  simp [Tm.zf]

@[simp] theorem Tm.subst_par (σ : Fin n → Tm m) (a : Tm n) :
    Syn.subst σ (Tm.par a) = Tm.par (Syn.subst σ a) := by
  simp [Tm.par]

@[simp] theorem Tm.subst_cyc (σ : Fin n → Tm m) (a : Tm n) :
    Syn.subst σ (Tm.cyc a) = Tm.cyc (Syn.subst σ a) := by
  simp [Tm.cyc]

@[simp] theorem Tm.subst_mod3 (σ : Fin n → Tm m) (a : Tm n) :
    Syn.subst σ (Tm.mod3 a) = Tm.mod3 (Syn.subst σ a) := by
  simp [Tm.mod3]

@[simp] theorem Tm.subst_ramp (σ : Fin n → Tm m) (a : Tm n) :
    Syn.subst σ (Tm.ramp a) = Tm.ramp (Syn.subst σ a) := by
  simp [Tm.ramp]

@[simp] theorem Tm.subst_hop (σ : Fin n → Tm m) (a : Tm n) :
    Syn.subst σ (Tm.hop a) = Tm.hop (Syn.subst σ a) := by
  simp [Tm.hop]

lift_op₁ zf par cyc mod3 ramp hop

namespace Q

variable {Γ : List (Fm Tm n)}

/-! ### The zero test and the parity -/

theorem zf_eq (x : Q Γ) : zf x = sel x 1 0 := by
  induction x using Q.ind with | _ a
  rfl

@[simp] theorem zf_zero : zf (0 : Q Γ) = 1 := by rw [zf_eq, sel_zero]

@[simp] theorem zf_succ (x : Q Γ) : zf (succ x) = 0 := by rw [zf_eq, sel_succ]

@[simp] theorem zf_one : zf (1 : Q Γ) = 0 := zf_succ 0

@[simp] theorem par_zero : par (0 : Q Γ) = 0 := by
  show mk Γ (Tm.par Tm.zero) = mk Γ Tm.zero
  exact sound (Teq.iterZero _ _)

@[simp] theorem par_succ (x : Q Γ) : par (succ x) = zf (par x) := by
  induction x using Q.ind with | _ a
  have h := Teq.iterSucc (Γ := Γ) a Tm.zero (Tm.zf (var 0))
  simp only [Tm.subst_zf, Syn.subst_var, Syn.inst_zero] at h
  exact sound h

@[simp] theorem par_one : par (1 : Q Γ) = 1 := by
  show par (succ 0) = 1
  rw [par_succ, par_zero, zf_zero]

/-- The parity is a Boolean: it is fixed by the double zero test. -/
@[simp] theorem zf_zf_par (x : Q Γ) : zf (zf (par x)) = par x := by
  induction x using Q.ind with | _ a
  have h := eqInd (Γ := Γ) (Tm.zf (Tm.zf (Tm.par (var 0)))) (Tm.par (var 0)) (by simp)
    (fun ih => by simp at ih; simp [ih]) a
  simpa using h

/-- Splitting the Boolean `par x`, over all extensions of the context. -/
theorem par_cases (x : Q Γ) {p q : Q Γ}
    (h0 : ∀ {k : ℕ} {Γ' : List (Fm Tm k)} (e : Ext Γ Γ'), par (e.map x) = 0 → e.map p = e.map q)
    (h1 : ∀ {k : ℕ} {Γ' : List (Fm Tm k)} (e : Ext Γ Γ'), par (e.map x) = 1 → e.map p = e.map q) :
    p = q := by
  refine Q.cases (par x) (fun e he => h0 e (by rwa [Ext.map_par] at he)) (fun e z he => h1 e ?_)
  rw [Ext.map_par] at he
  have h := zf_zf_par (e.map x)
  rw [he, zf_succ, zf_zero] at h
  rw [he, ← h]

theorem par_double (x : Q Γ) : par (x + x) = 0 := by
  induction x using Q.ind with | _ a
  have h := eqInd (Γ := Γ) (Tm.par (Tm.add (var 0) (var 0))) Tm.zero (by simp)
    (fun ih => by simp at ih; simp [ih]) a
  simpa using h

theorem par_triple (x : Q Γ) : par (x + x + x) = par x := by
  induction x using Q.ind with | _ a
  have h := eqInd (Γ := Γ) (Tm.par (Tm.add (Tm.add (var 0) (var 0)) (var 0))) (Tm.par (var 0))
    (by simp) (fun ih => by simp at ih; simp [ih]) a
  simpa using h

/-! ### The three-cycle -/

theorem cyc_eq (x : Q Γ) : cyc x = zf x + (par x + par x) := by
  induction x using Q.ind with | _ a
  rfl

@[simp] theorem cyc_zero : cyc (0 : Q Γ) = 1 := by simp [cyc_eq]

@[simp] theorem cyc_one : cyc (1 : Q Γ) = succ 1 := by simp [cyc_eq]

@[simp] theorem cyc_succ_one : cyc (succ (1 : Q Γ)) = 0 := by simp [cyc_eq]

@[simp] theorem mod3_zero : mod3 (0 : Q Γ) = 0 := by
  show mk Γ (Tm.mod3 Tm.zero) = mk Γ Tm.zero
  exact sound (Teq.iterZero _ _)

@[simp] theorem mod3_succ (x : Q Γ) : mod3 (succ x) = cyc (mod3 x) := by
  induction x using Q.ind with | _ a
  have h := Teq.iterSucc (Γ := Γ) a Tm.zero (Tm.cyc (var 0))
  simp only [Tm.subst_cyc, Syn.subst_var, Syn.inst_zero] at h
  exact sound h

/-! ### The ramp -/

@[simp] theorem ramp_zero : ramp (0 : Q Γ) = 0 := by
  show mk Γ (Tm.ramp Tm.zero) = mk Γ Tm.zero
  exact sound (Teq.iterZero _ _)

theorem ramp_succ_mod3 (x : Q Γ) : ramp (succ x) = succ (ramp x + mod3 (ramp x)) := by
  induction x using Q.ind with | _ a
  have h := Teq.iterSucc (Γ := Γ) a Tm.zero (Tm.succ (Tm.add (var 0) (Tm.mod3 (var 0))))
  simp only [Tm.subst_succ, Tm.subst_add, Tm.subst_mod3, Syn.subst_var, Syn.inst_zero] at h
  exact sound h

/-- The ramp invariant: the residue of the ramp is the parity of its counter. -/
@[simp] theorem mod3_ramp (x : Q Γ) : mod3 (ramp x) = par x := by
  induction x using Q.ind with | _ a
  have h := eqInd (Γ := Γ) (Tm.mod3 (Tm.ramp (var 0))) (Tm.par (var 0)) (by simp)
    (fun ih => by
      simp at ih
      simp [ramp_succ_mod3, ih]
      refine par_cases (mk _ (var 0)) ?_ ?_ <;> intro k Γ' e he <;>
        have ih' := congrArg e.map ih <;> simp [he] at ih' ⊢ <;> simp [ih']) a
  simpa using h

@[simp] theorem ramp_succ (x : Q Γ) : ramp (succ x) = succ (ramp x + par x) := by
  rw [ramp_succ_mod3, mod3_ramp]

theorem ramp_double (x : Q Γ) : ramp (x + x) = x + x + x := by
  induction x using Q.ind with | _ a
  have h := eqInd (Γ := Γ) (Tm.ramp (Tm.add (var 0) (var 0)))
    (Tm.add (Tm.add (var 0) (var 0)) (var 0)) (by simp)
    (fun ih => by simp at ih; simp [ih, par_double]) a
  simpa using h

theorem ramp_triple (x : Q Γ) : ramp (x + x + x) = ramp x + ramp x + ramp x + par x := by
  induction x using Q.ind with | _ a
  have h := eqInd (Γ := Γ) (Tm.ramp (Tm.add (Tm.add (var 0) (var 0)) (var 0)))
    (Tm.add (Tm.add (Tm.add (Tm.ramp (var 0)) (Tm.ramp (var 0))) (Tm.ramp (var 0)))
      (Tm.par (var 0)))
    (by simp)
    (fun ih => by
      simp at ih
      simp [ih, par_triple]
      refine par_cases (mk _ (var 0)) ?_ ?_ <;> intro k Γ' e he <;> simp [he]) a
  simpa using h

/-! ### The factor map -/

theorem hop_eq (x : Q Γ) : hop x = sel (par x) (ramp x) x := by
  induction x using Q.ind with | _ a
  rfl

theorem hop_double (x : Q Γ) : hop (x + x) = x + x + x := by
  rw [hop_eq, par_double, sel_zero, ramp_double]

@[simp] theorem hop_one : hop (1 : Q Γ) = 1 := by
  rw [hop_eq, par_one, sel_one]

theorem hop_triple (x : Q Γ) : hop (x + x + x) = hop x + hop x + hop x := by
  simp only [hop_eq, par_triple, ramp_triple]
  refine par_cases x ?_ ?_ <;> intro k Γ' e he <;> simp [he]

end Q

end LeanProofs.ConciseIPRA
