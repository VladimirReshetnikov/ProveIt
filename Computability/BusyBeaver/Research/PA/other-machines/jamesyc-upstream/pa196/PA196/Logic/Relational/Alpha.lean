module
public import PA196.Logic.Relational.Substitution
@[expose] public section

namespace PA196.Logic.Relational
open M6.PA.NativeCalculus (renameLabel)

theorem names_free_false (p : Named) (v : Nat) (h : p.names v = false) : p.free v = false := by
  cases hf : p.free v with
  | false => rfl
  | true => have hn := p.free_in_names v hf; rw [h] at hn; contradiction

theorem names_binders_false (p : Named) (v : Nat) (h : p.names v = false) : p.binders v = false := by
  cases hb : p.binders v with
  | false => rfl
  | true => have hn := p.binders_in_names v hb; rw [h] at hn; contradiction

theorem replace_free (p : Named) (x y : Nat) (hxy : x ≠ y) :
    (p.replace x y).free x = false := by
  have havoid (a : Nat) : x ≠ renameLabel x y a := by
    by_cases ha : a = x
    · simpa [renameLabel,ha] using hxy
    · simpa [renameLabel,ha] using Ne.symm ha
  induction p <;> simp_all [M6.PA.NativeCalculus.Named.replace,M6.PA.NativeCalculus.Named.free]

theorem replace_reserved (p : Named) (z x y : Nat)
    (hz : p.names z = false) (hzy : z ≠ y) : (p.replace x y).names z = false := by
  induction p with
  | truth => rfl
  | neg p ih => exact ih hz
  | imp p q ihp ihq =>
    simp only [M6.PA.NativeCalculus.Named.names,Bool.or_eq_false_iff] at hz
    exact Bool.or_eq_false_iff.mpr ⟨ihp hz.1,ihq hz.2⟩
  | mem a b | eq a b =>
    simp only [M6.PA.NativeCalculus.Named.names,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hz
    simp only [M6.PA.NativeCalculus.Named.replace,M6.PA.NativeCalculus.Named.names,Bool.or_eq_false_iff,beq_eq_false_iff_ne]
    exact ⟨reserved_rename z x y a hz.1 hzy,reserved_rename z x y b hz.2 hzy⟩
  | all a p ih =>
    simp only [M6.PA.NativeCalculus.Named.names,Bool.or_eq_false_iff] at hz
    exact Bool.or_eq_false_iff.mpr ⟨hz.1,ih hz.2⟩

def relationalUniversalInstance (p : Named) (z x y : Nat) (hxy : x ≠ y)
    (hz : p.names z = false) (hzx : z ≠ x) (hzy : z ≠ y)
    (hx : p.binders x = false) (hy : p.binders y = false) :
    Proof (wim (wal x (relationalCode z p)) (relationalCode z (p.replace x y))) := by
  let r := relationalCode z (p.replace x y)
  let hv : Proof (wim r (wal x r)) :=
    relationalCodeVacuity (p.replace x y) z x (Ne.symm hzx)
      (replace_free p x y hxy) (by simpa [M6.PA.NativeCalculus.Named.replace_binders] using hx)
  let hsub := (relationalReplace p z x y hz hzx hzy hx hy).1
  let he : Context [neighborhoodEquality x y z,relationalCode z p]
      (neighborhoodEquality x y z) := .assumption (by simp)
  let hp : Context [neighborhoodEquality x y z,relationalCode z p]
      (relationalCode z p) := .assumption (by simp)
  let hperm : Proof (wim (relationalCode z p) (wim (neighborhoodEquality x y z) r)) :=
    (Context.mp hp (.mp he (.closed hsub))).deduction.deduction.empty
  let hall : Context [wal x (relationalCode z p)] (wal x (relationalCode z p)) := .assumption (by simp)
  let hrel := hall.forallMP x (.closed (.all x hperm))
  exact (Context.existsElim x hv hrel (.closed (neighborhoodWitness x y z hzx hzy))).deduction.empty

def relationalUniversalAlpha (p : Named) (z x y : Nat) (hxy : x ≠ y)
    (hz : p.names z = false) (hzx : z ≠ x) (hzy : z ≠ y)
    (hx : p.binders x = false) (hy : p.names y = false) :
    Proof (wim (wal x (relationalCode z p)) (wal y (relationalCode z (p.replace x y)))) ×
    Proof (wim (wal y (relationalCode z (p.replace x y))) (wal x (relationalCode z p))) := by
  have hyb := names_binders_false p y hy
  have hyf := names_free_false p y hy
  let f : Context [wal x (relationalCode z p)] (relationalCode z (p.replace x y)) :=
    .mp (.assumption (by simp)) (.closed (relationalUniversalInstance p z x y hxy hz hzx hzy hx hyb))
  let vf : Proof (wim (wal x (relationalCode z p)) (wal y (wal x (relationalCode z p)))) :=
    relationalCodeVacuity (.all x p) z y (Ne.symm hzy)
      (by simp [M6.PA.NativeCalculus.Named.free,hyf]) (by simp [M6.PA.NativeCalculus.Named.binders,hyb,Ne.symm hxy])
  let reverseInstance : Proof (wim (wal y (relationalCode z (p.replace x y))) (relationalCode z p)) := by
    simpa only [p.replace_roundtrip x y hy] using
      relationalUniversalInstance (p.replace x y) z y x (Ne.symm hxy)
        (replace_reserved p z x y hz hzy) hzy hzx
        (by simpa [M6.PA.NativeCalculus.Named.replace_binders] using hyb) (by simpa [M6.PA.NativeCalculus.Named.replace_binders] using hx)
  let b : Context [wal y (relationalCode z (p.replace x y))] (relationalCode z p) :=
    .mp (.assumption (by simp)) (.closed reverseInstance)
  let vb : Proof (wim (wal y (relationalCode z (p.replace x y)))
      (wal x (wal y (relationalCode z (p.replace x y))))) :=
    relationalCodeVacuity (.all y (p.replace x y)) z x (Ne.symm hzx)
      (by simp [M6.PA.NativeCalculus.Named.free,replace_free p x y hxy])
      (by simp [M6.PA.NativeCalculus.Named.binders,M6.PA.NativeCalculus.Named.replace_binders,hx,hxy])
  exact ⟨(f.generalizeSingleton y vf).deduction.empty,
    (b.generalizeSingleton x vb).deduction.empty⟩

#print axioms relationalUniversalInstance
#print axioms relationalUniversalAlpha
end PA196.Logic.Relational

