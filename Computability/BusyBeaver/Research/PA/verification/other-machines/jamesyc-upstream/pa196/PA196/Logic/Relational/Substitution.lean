module
public import PA196.Logic.Relational.Atoms
@[expose] public section

namespace PA196.Logic.Relational
def _root_.PA196.Logic.Context.implicationCongruence {Γ : List Nat} {a aa b bb : Nat}
    (p : Context Γ (wim aa a)) (q : Context Γ (wim b bb)) :
    Context Γ (wim (wim a b) (wim aa bb)) := by
  let h : Context (aa :: wim a b :: Γ) aa := .assumption (by simp)
  let hab : Context (aa :: wim a b :: Γ) (wim a b) := .assumption (by simp)
  exact (Context.mp (.mp (.mp h ((p.up (wim a b)).up aa)) hab)
    ((q.up (wim a b)).up aa)).deduction.deduction

def conditionalContrapose {e a b : Nat} (p : Proof (wim e (wim a b))) :
    Proof (wim e (wim (wn b) (wn a))) := by
  let h : Context [e] e := .assumption (by simp)
  exact (Context.mp (.mp h (.closed p)) (.closed (contraposition a b))).deduction.empty

def conditionalImplicationCongruence {e a aa b bb : Nat}
    (p : Proof (wim e (wim aa a))) (q : Proof (wim e (wim b bb))) :
    Proof (wim e (wim (wim a b) (wim aa bb))) := by
  let h : Context [e] e := .assumption (by simp)
  exact (Context.implicationCongruence (.mp h (.closed p)) (.mp h (.closed q))).deduction.empty

def conditionalUniversal {e a b : Nat} (x : Nat)
    (hv : Proof (wim e (wal x e))) (p : Proof (wim e (wim a b))) :
    Proof (wim e (wim (wal x a) (wal x b))) := by
  let he : Context [wal x a, e] e := .assumption (by simp)
  let ha : Context [wal x a, e] (wal x a) := .assumption (by simp)
  let hwe : Context [wal x a, e] (wal x e) := .mp he (.closed hv)
  let hstep := hwe.forallMP x (.closed (.all x p))
  exact (ha.forallMP x hstep).deduction.deduction.empty


def relationalReplace (p : Named) (z x y : Nat)
    (hz : p.names z = false) (hzx : z ≠ x) (hzy : z ≠ y)
    (hx : p.binders x = false) (hy : p.binders y = false) :
    Proof (wim (neighborhoodEquality x y z)
      (wim (relationalCode z p) (relationalCode z (p.replace x y)))) ×
    Proof (wim (neighborhoodEquality x y z)
      (wim (relationalCode z (p.replace x y)) (relationalCode z p))) :=
  match p with
  | .truth => ⟨(Context.closed (Γ := [neighborhoodEquality x y z]) (identity 0)).deduction.empty,
      (Context.closed (Γ := [neighborhoodEquality x y z]) (identity 0)).deduction.empty⟩
  | .mem a b => by
    simp only [M6.PA.NativeCalculus.Named.names,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hz
    exact relationalRenameMembership z x y a b hz.1 hz.2 hzy
  | .eq a b => relationalRenameEquality z x y a b
  | .neg p =>
    let hs := relationalReplace p z x y hz hzx hzy hx hy
    ⟨conditionalContrapose hs.2,conditionalContrapose hs.1⟩
  | .imp p q => by
    simp only [M6.PA.NativeCalculus.Named.names,M6.PA.NativeCalculus.Named.binders,Bool.or_eq_false_iff] at hz hx hy
    let hp := relationalReplace p z x y hz.1 hzx hzy hx.1 hy.1
    let hq := relationalReplace q z x y hz.2 hzx hzy hx.2 hy.2
    exact ⟨conditionalImplicationCongruence hp.2 hq.1,
      conditionalImplicationCongruence hp.1 hq.2⟩
  | .all a p => by
    simp only [M6.PA.NativeCalculus.Named.names,M6.PA.NativeCalculus.Named.binders,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hz hx hy
    let hp := relationalReplace p z x y hz.2 hzx hzy hx.2 hy.2
    let hv := neighborhoodEqualityVacuity x y z a (Ne.symm hx.1) (Ne.symm hy.1) (Ne.symm hz.1)
    exact ⟨conditionalUniversal a hv hp.1,conditionalUniversal a hv hp.2⟩

#print axioms relationalReplace
end PA196.Logic.Relational
