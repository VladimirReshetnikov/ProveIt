module
public import M6PA.Calibration.NativeNamedInterpretation
public import M6PA.Theory
public import M6PA.Calibration.ActualRelationalWitness
public import M6.Logic.NativeNames
@[expose] public section

/-! A structural named-formula to numeric relational-code compiler. A user
of this compiler must reserve z outside all original names; no semantic or
whole-proof translation correctness is asserted here. The theorem proves the
finite actual-basis vacuity obligation for every source constructor, including
equality via its explicit neighborhood replacement rather than primitive EqV. -/
namespace M6.PA.NativeCalculus.ActualBasis

def relationalCode (z : Nat) : Named → Nat
  | .truth => 0
  | .imp p q => wim (relationalCode z p) (relationalCode z q)
  | .neg p => wn (relationalCode z p)
  | .mem a b => wel a b
  | .eq a b => neighborhoodEquality a b z
  | .all a p => wal a (relationalCode z p)

def truthProof : Proof 0 := by
  simpa only [wim,M6.Source.Cantor.implication,M6.Source.Cantor.pair,
    M6.Source.Cantor.triangle,Nat.add_zero,Nat.mul_zero] using identity 0

def relationalCodeVacuity (p : Named) (z v : Nat) (hvz : v ≠ z)
    (hf : p.free v = false) (hb : p.binders v = false) :
    Proof (wim (relationalCode z p) (wal v (relationalCode z p))) :=
  match p with
  | .truth => .mp (.all v truthProof) (Dominated.k (wal v 0) 0)
  | .neg p => negationVacuity v _ (relationalCodeVacuity p z v hvz hf hb)
  | .imp p q => by
    simp only [Named.free,Named.binders,Bool.or_eq_false_iff] at hf hb
    exact implicationVacuity v _ _ (relationalCodeVacuity p z v hvz hf.1 hb.1)
      (relationalCodeVacuity q z v hvz hf.2 hb.2)
  | .mem a b => by
    simp only [Named.free,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hf
    exact membershipVacuity a b v hf.1 hf.2
  | .eq a b => by
    simp only [Named.free,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hf
    exact neighborhoodEqualityVacuity a b z v hf.1 hf.2 hvz
  | .all a p => by
    simp only [Named.binders,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hb
    have hfp : p.free v = false := by simpa [Named.free,hb.1] using hf
    exact universalVacuity v a _ (relationalCodeVacuity p z v hvz hfp hb.2)

#print axioms truthProof
#print axioms relationalCodeVacuity
end M6.PA.NativeCalculus.ActualBasis

