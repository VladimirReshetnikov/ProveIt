module
public import M6.Logic.NativeEquality
@[expose] public section

/-! Finite numeric equality substitution through every named connective.
The quantified branch uses actual guarded-bundle equality vacuity and R2;
it does not replace a proof compiler with semantic completeness. -/
namespace M6.PA.NativeCalculus

def Context.implicationCongruence {Γ : List Nat} {a aa b bb : Nat}
    (p : Context Γ (wim aa a)) (q : Context Γ (wim b bb)) :
    Context Γ (wim (wim a b) (wim aa bb)) := by
  let h : Context (aa :: wim a b :: Γ) aa := .assumption (by simp)
  let hab : Context (aa :: wim a b :: Γ) (wim a b) := .assumption (by simp)
  exact (Context.mp (.mp (.mp h ((p.up (wim a b)).up aa)) hab)
    ((q.up (wim a b)).up aa)).deduction.deduction

def conditionalContrapose {e a b : Nat} (p : Derivation (wim e (wim a b))) :
    Derivation (wim e (wim (wn b) (wn a))) := by
  let h : Context [e] e := .assumption (by simp)
  exact (Context.mp (.mp h (.closed p)) (.closed (contraposition a b))).deduction.empty

def conditionalImplicationCongruence {e a aa b bb : Nat}
    (p : Derivation (wim e (wim aa a))) (q : Derivation (wim e (wim b bb))) :
    Derivation (wim e (wim (wim a b) (wim aa bb))) := by
  let h : Context [e] e := .assumption (by simp)
  exact (Context.implicationCongruence (.mp h (.closed p)) (.mp h (.closed q))).deduction.empty

def conditionalUniversal {e a b : Nat} (x : Nat)
    (hv : Derivation (wim e (wal x e))) (p : Derivation (wim e (wim a b))) :
    Derivation (wim e (wim (wal x a) (wal x b))) := by
  let he : Context [wal x a, e] e := .assumption (by simp)
  let ha : Context [wal x a, e] (wal x a) := .assumption (by simp)
  let hwe : Context [wal x a, e] (wal x e) := .mp he (.closed hv)
  let hstep := hwe.forallMP x (.closed (.all x p))
  exact (ha.forallMP x hstep).deduction.deduction.empty

/-- Two actual proof trees, not just semantic equivalence. Binder conditions
are the exact capture restrictions of the retained named compiler. -/
def Named.equalityReplace (p : Named) (x y : Nat)
    (hx : p.binders x = false) (hy : p.binders y = false) :
    Derivation (wim (weq x y) (wim p.encode (p.replace x y).encode)) ×
    Derivation (wim (weq x y) (wim (p.replace x y).encode p.encode)) :=
  match p with
  | .truth => by
    exact ⟨(Context.closed (Γ := [weq x y]) (identity 0)).deduction.empty,
      (Context.closed (Γ := [weq x y]) (identity 0)).deduction.empty⟩
  | .mem a b => ⟨renameMembershipForward x y a b,renameMembershipReverse x y a b⟩
  | .eq a b => ⟨renameEqualityForward x y a b,renameEqualityReverse x y a b⟩
  | .neg p =>
    let hs := p.equalityReplace x y hx hy
    ⟨conditionalContrapose hs.2,conditionalContrapose hs.1⟩
  | .imp p q => by
    simp only [binders,Bool.or_eq_false_iff] at hx hy
    let hp := p.equalityReplace x y hx.1 hy.1
    let hq := q.equalityReplace x y hx.2 hy.2
    exact ⟨conditionalImplicationCongruence hp.2 hq.1,
      conditionalImplicationCongruence hp.1 hq.2⟩
  | .all a p => by
    simp only [binders,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hx hy
    let hp := p.equalityReplace x y hx.2 hy.2
    let hv := equalityVacuity x y a (Ne.symm hx.1) (Ne.symm hy.1)
    exact ⟨conditionalUniversal a hv hp.1,conditionalUniversal a hv hp.2⟩

#print axioms Named.equalityReplace
#print axioms conditionalUniversal
end M6.PA.NativeCalculus

