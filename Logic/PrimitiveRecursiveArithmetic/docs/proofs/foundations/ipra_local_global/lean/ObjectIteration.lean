import ObjectKernel

/-!
An actual object-iPRA proof transformer for primitive recursion.
No semantic truth-to-provability principle is assumed.
Invariant variables: state, time, then parameters.
-/

namespace LeanProofs.ConciseIPRA.LocalGlobal

open Syn
open scoped Fm

theorem subst_cases {k n m : Nat} (s : PTm n)
    (ts : Fin k → PTm n) (σ : Fin n → PTm m) :
    (fun i => Syn.subst σ (Fin.cases s ts i)) =
      Fin.cases (Syn.subst σ s) (fun i => Syn.subst σ (ts i)) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem qf_subst {n m : Nat} {P : Fm PTm n} (h : P.QF)
    (σ : Fin n → PTm m) : (P.subst σ).QF := by
  induction P generalizing m with
  | eq => trivial
  | bot => trivial
  | and P Q ihP ihQ => exact ⟨ihP h.1 σ, ihQ h.2 σ⟩
  | or P Q ihP ihQ => exact ⟨ihP h.1 σ, ihQ h.2 σ⟩
  | imp P Q ihP ihQ => exact ⟨ihP h.1 σ, ihQ h.2 σ⟩
  | all => exact False.elim h
  | ex => exact False.elim h

def runTerm {k n : Nat} (f : PR k) (g : PR (k + 2))
    (t : PTm n) (xs : Fin k → PTm n) : PTm n :=
  PTm.app (.prec f g) (Fin.cases t xs)

def instStateTime {k n : Nat} (P : Fm PTm (k + 2))
    (s t : PTm n) (xs : Fin k → PTm n) : Fm PTm n :=
  P.subst (Fin.cases s (Fin.cases t xs))

def runInvariant {k : Nat} (f : PR k) (g : PR (k + 2))
    (P : Fm PTm (k + 2)) : Fm PTm (k + 1) :=
  instStateTime P (runTerm f g (var 0) (fun i => var i.succ))
    (var 0) (fun i => var i.succ)

def baseFormula {k : Nat} (f : PR k) (P : Fm PTm (k + 2)) : Fm PTm k :=
  instStateTime P (PTm.app f var) PTm.zero var

def nextFormula {k : Nat} (g : PR (k + 2)) (P : Fm PTm (k + 2)) :
    Fm PTm (k + 2) :=
  instStateTime P
    (PTm.app g (Fin.cases (var 1) (Fin.cases (var 0) (fun i => var i.succ.succ))))
    (PTm.succ (var 1)) (fun i => var i.succ.succ)

@[simp] theorem subst_runTerm {k n m : Nat} (f : PR k) (g : PR (k + 2))
    (t : PTm n) (xs : Fin k → PTm n) (σ : Fin n → PTm m) :
    Syn.subst σ (runTerm f g t xs) =
      runTerm f g (Syn.subst σ t) (fun i => Syn.subst σ (xs i)) := by
  simp only [runTerm, PTm.subst_app]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

@[simp] theorem subst_instStateTime {k n m : Nat} (P : Fm PTm (k + 2))
    (s t : PTm n) (xs : Fin k → PTm n) (σ : Fin n → PTm m) :
    (instStateTime P s t xs).subst σ =
      instStateTime P (Syn.subst σ s) (Syn.subst σ t)
        (fun i => Syn.subst σ (xs i)) := by
  unfold instStateTime
  rw [Fm.subst_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact Fin.cases rfl (fun _ => rfl) j

theorem stateCongr {k n : Nat} {Γ : List (Fm PTm n)}
    (P : Fm PTm (k + 2)) (s s' t : PTm n) (xs : Fin k → PTm n)
    (e : Γ ⊢[PRAAx] s ≐ s')
    (h : Γ ⊢[PRAAx] instStateTime P s t xs) :
    Γ ⊢[PRAAx] instStateTime P s' t xs := by
  exact Prf.eqSubst P _ _
    (fun i => Fin.cases e (fun _ => Prf.eqRefl _) i) h

/-- Verified local-to-global rule. The hypotheses are *object derivations*.
    Arbitrary assumptions Γ are allowed; the numerical invariant P is QF. -/
theorem primitiveRecursionInvariant {k : Nat} (f : PR k) (g : PR (k + 2))
    (P : Fm PTm (k + 2)) (hP : P.QF) (Γ : List (Fm PTm k))
    (h0 : Γ ⊢[PRAAx] baseFormula f P)
    (hS : P :: (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] nextFormula g P) :
    Γ ⊢[PRAAx] Fm.all (runInvariant f g P) := by
  apply PRA.qfInd (runInvariant f g P)
  · exact qf_subst hP _
  · have e := PRA.precZero (Γ := Γ) f g (var : Fin k → PTm k)
    have h := stateCongr P (PTm.app f var) (runTerm f g PTm.zero var)
      PTm.zero var (Prf.eqSymm e) h0
    simpa [runInvariant] using h
  · let R := runInvariant f g P
    let σ : Fin (k + 2) → PTm (k + 1) :=
      Fin.cases (runTerm f g (var 0) (fun i => var i.succ)) var
    have hσ : P.subst σ = R := by
      unfold R runInvariant instStateTime
      congr 1
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact Fin.cases rfl (fun _ => rfl) j
    have hlocal := hS.substWeaken σ (Δ := R :: Γ.map Fm.shift) (by
      intro A hA
      simp only [List.map_cons, List.mem_cons] at hA
      rcases hA with hA | hA
      · exact List.mem_cons.mpr (Or.inl (hA.trans hσ))
      · right
        rcases List.mem_map.mp hA with ⟨B, hB, rfl⟩
        rcases List.mem_map.mp hB with ⟨C, hC, rfl⟩
        rcases List.mem_map.mp hC with ⟨D, hD, rfl⟩
        have e : D.shift.shift.subst σ = D.shift := by
          simp only [Fm.subst_shift]
          rfl
        rw [e]
        exact List.mem_map_of_mem hD)
    have e := PRA.precSucc (Γ := R :: Γ.map Fm.shift) f g
      (var 0 : PTm (k + 1)) (fun i => var i.succ)
    have hlocal' : R :: Γ.map Fm.shift ⊢[PRAAx]
        instStateTime P
          (PTm.app g (Fin.cases (var 0)
            (Fin.cases (runTerm f g (var 0) (fun i => var i.succ))
              (fun i => var i.succ))))
          (PTm.succ (var 0)) (fun i => var i.succ) := by
      simpa [nextFormula, σ, subst_cases] using hlocal
    have hout := stateCongr P _ (runTerm f g (PTm.succ (var 0))
      (fun i => var i.succ)) (PTm.succ (var 0)) (fun i => var i.succ)
      (Prf.eqSymm e) hlocal'
    simpa [R, runInvariant] using hout

/-- Instantiate the quantified result at any PR term used as a fuel bound. -/
theorem primitiveRecursionAt {k : Nat} (f : PR k) (g : PR (k + 2))
    (P : Fm PTm (k + 2)) (hP : P.QF) (Γ : List (Fm PTm k))
    (h0 : Γ ⊢[PRAAx] baseFormula f P)
    (hS : P :: (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] nextFormula g P)
    (fuel : PTm k) :
    Γ ⊢[PRAAx] instStateTime P (runTerm f g fuel var) fuel var := by
  have h := Prf.allE fuel (primitiveRecursionInvariant f g P hP Γ h0 hS)
  simpa [runInvariant] using h

end LeanProofs.ConciseIPRA.LocalGlobal
