import PA194LogicVacuity
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194Logic

def specializeWithMirroredEquality (z c atom target : Nat)
    (hv : Derivation (wim target (wal z target)))
    (hr : Derivation (wim (weq c z) (wim atom target))) :
    Derivation (wim (wal z atom) target) := by
  let hs : Derivation (wim atom (wim (weq c z) target)) :=
    .mp hr (Dominated.exchange (weq c z) atom target)
  let hu : Context [wal z atom] (wal z atom) := .assumption (by simp)
  let ht : Context [wal z atom] (wal z (wim (weq c z) target)) :=
    hu.forallMP z (.closed (.all z hs))
  exact (Context.existsElim z hv ht (.closed (r1 z c))).deduction.empty

/-- Specialization of a negative membership property needs direct rewriting only. -/
def negativeSpecialization (y v c p q : Nat) (hcy : y ≠ c) (hvy : y ≠ v)
    (hr : Derivation (wim (weq v y) (wim q p)))
    (hv : Derivation (wim q (wal y q))) :
    Derivation (wim (wal y (wim (wel c y) (wn p))) (wim (wel c v) (wn q))) := by
  let e := weq v y
  let py := wim (wel c y) (wn p)
  let he : Context [q,wel c v,py,e] e := .assumption (by simp)
  let hq : Context [q,wel c v,py,e] q := .assumption (by simp)
  let hm : Context [q,wel c v,py,e] (wel c v) := .assumption (by simp)
  let hy : Context [q,wel c v,py,e] py := .assumption (by simp)
  let hmy := Context.mp hm (.mp he (.closed (memRight v y c)))
  let hp := Context.mp hq (.mp he (.closed hr))
  let contra := Context.mp hp (.mp hmy hy)
  let hh : Derivation (wim e (wim py (wim (wel c v) (wn q)))) :=
    contra.deduction.deduction.deduction.deduction.empty
  exact specializeWithMirroredEquality y v py (wim (wel c v) (wn q))
    (implicationVacuity y _ _ (membershipVacuity c v y hcy hvy)
      (negationVacuity y q hv)) hh


#print axioms specializeWithMirroredEquality
#print axioms negativeSpecialization
end PA194Logic
