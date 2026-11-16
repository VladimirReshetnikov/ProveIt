module
public import PA196.Logic.Relational.Interface
public import M6.Logic.NativeNames
@[expose] public section
namespace PA196.Logic.Relational
abbrev Named := M6.PA.NativeCalculus.Named
abbrev Proof := PA196.Logic.Derivation

def relationalCode (z : Nat) : Named → Nat
  | .truth => 0
  | .imp p q => wim (relationalCode z p) (relationalCode z q)
  | .neg p => wn (relationalCode z p)
  | .mem a b => wel a b
  | .eq a b => neighborhoodEquality a b z
  | .all a p => wal a (relationalCode z p)

def truthProof : Proof 0 := identity 0

def relationalCodeVacuity (p : Named) (z v : Nat) (hvz : v ≠ z)
    (hf : p.free v = false) (hb : p.binders v = false) :
    Proof (wim (relationalCode z p) (wal v (relationalCode z p))) :=
  match p with
  | .truth => .mp (.all v truthProof) (Dominated.k (wal v 0) 0)
  | .neg p => negationVacuity v _ (relationalCodeVacuity p z v hvz hf hb)
  | .imp p q => by
    simp only [M6.PA.NativeCalculus.Named.free,M6.PA.NativeCalculus.Named.binders,Bool.or_eq_false_iff] at hf hb
    exact implicationVacuity v _ _ (relationalCodeVacuity p z v hvz hf.1 hb.1)
      (relationalCodeVacuity q z v hvz hf.2 hb.2)
  | .mem a b => by
    simp only [M6.PA.NativeCalculus.Named.free,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hf
    exact membershipVacuity a b v hf.1 hf.2
  | .eq a b => by
    simp only [M6.PA.NativeCalculus.Named.free,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hf
    exact neighborhoodEqualityVacuity a b z v hf.1 hf.2 hvz
  | .all a p => by
    simp only [M6.PA.NativeCalculus.Named.binders,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hb
    have hfp : p.free v = false := by simpa [M6.PA.NativeCalculus.Named.free,hb.1] using hf
    exact universalVacuity v a _ (relationalCodeVacuity p z v hvz hfp hb.2)

#print axioms truthProof
#print axioms relationalCodeVacuity
end PA196.Logic.Relational

