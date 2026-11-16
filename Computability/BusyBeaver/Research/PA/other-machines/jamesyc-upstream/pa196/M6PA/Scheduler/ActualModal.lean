module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualPropositional
@[expose] public section
open M6.Arithmetic.PA

/-! Dependency-minimal modal rules in the actual-only proof datatype.
No historical equality reflexivity, rho7, vacuity or bundle is available. -/
namespace M6.PA.NativeCalculus.ActualCore

def negationVacuity (x a : Nat) (hv : Proof (wim a (wal x a))) :
    Proof (wim (wn a) (wal x (wn a))) := by
  let hc := contrapose hv
  let hg := Proof.all x hc
  let hl := Proof.mp hg (Proof.r2 x (wn (wal x a)) (wn a))
  let hr := contrapose (Proof.r6 x a)
  let hf := implicationCompose hr (doubleNegationElimination (wal x (wn (wal x a))))
  exact implicationCompose hf hl

def Context.existsElim {Γ : List Nat} (x : Nat) {a b : Nat}
    (hv : Proof (wim b (wal x b)))
    (p : Context Γ (wal x (wim a b))) (q : Context Γ (wex x a)) : Context Γ b := by
  let hn : Context (wn b :: Γ) (wn b) := .assumption (by simp)
  let hnb : Context (wn b :: Γ) (wal x (wn b)) :=
    .mp hn (.closed (negationVacuity x b hv))
  let hc : Context (wn b :: Γ) (wal x (wim (wn b) (wn a))) :=
    (p.up (wn b)).forallMP x (.closed (.all x (contraposition a b)))
  let ha : Context (wn b :: Γ) (wal x (wn a)) := hnb.forallMP x hc
  exact (Context.mp ha (q.up (wn b))).deduction.dne

def existentialMonotonicity (x : Nat) {a b : Nat} (p : Proof (wim a b)) :
    Proof (wim (wex x a) (wex x b)) :=
  contrapose (.mp (.all x (contrapose p)) (.r2 x (wn b) (wn a)))

#print axioms existentialMonotonicity
#print axioms Context.existsElim
end M6.PA.NativeCalculus.ActualCore

