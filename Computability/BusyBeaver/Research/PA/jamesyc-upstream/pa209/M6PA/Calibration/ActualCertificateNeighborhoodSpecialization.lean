module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateNeighborhoodWitness
@[expose] public section

/-! Generic finite universal specialization/alpha recipes. Actual conditional
replacement and actual vacuity certificates remain explicit inputs. -/
namespace M6.PA.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCheckerBlueprint ActualHeadGraphs
universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def universalSpecializeNeighborhood (x y z a b : V)
    (hzx : z ≠ x) (hzy : z ≠ y)
    (hr : Certificate (wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr x y z 0)
      (wim a b))) (hv : Certificate (wim b (wal x b))) :
    Certificate (wim (wal x a) b) := by
  let e := ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr x y z 0
  let he : Context [e,a] e := .assumption (by simp)
  let ha : Context [e,a] a := .assumption (by simp)
  let hs : Certificate (wim a (wim e b)) :=
    (Context.mp ha (.mp he (.closed hr))).deduction.deduction.empty
  let hu : Context [wal x a] (wal x a) := .assumption (by simp)
  let ht : Context [wal x a] (wal x (wim e b)) :=
    hu.forallMP x (.closed (.all x hs))
  exact (Context.existsElim x hv ht (.closed (neighborhoodWitness x y z hzx hzy))).deduction.empty

noncomputable def Context.generalizeSingleton {a b : V} (p : Context [a] b) (x : V)
    (hv : Certificate (wim a (wal x a))) : Context [a] (wal x b) :=
  p.generalize x (fun h hh => by
    have he : h = a := List.mem_singleton.mp hh
    subst h
    exact hv)

/-- A schematic two-way alpha recipe. The two genuine conditional replacement
certificates and two genuine vacuity certificates are not discharged here. -/
noncomputable def universalAlphaNeighborhood (x y z a b : V)
    (hzx : z ≠ x) (hzy : z ≠ y)
    (hf : Certificate (wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr x y z 0)
      (wim a b)))
    (hb : Certificate (wim (ActualArithmeticGraph.eval RelationalSource.Numeric.neighborhoodExpr x y z 0)
      (wim b a)))
    (hbx : Certificate (wim b (wal x b))) (hay : Certificate (wim a (wal y a))) :
    Certificate (wim (wal x a) (wal y b)) × Certificate (wim (wal y b) (wal x a)) := by
  let f : Context [wal x a] b := .mp (.assumption (by simp))
    (.closed (universalSpecializeNeighborhood x y z a b hzx hzy hf hbx))
  let hreverse := implicationCompose (neighborhoodSymmetry y x z) hb
  let r : Context [wal y b] a := .mp (.assumption (by simp))
    (.closed (universalSpecializeNeighborhood y x z b a hzy hzx hreverse hay))
  exact ⟨(f.generalizeSingleton y (universalVacuity y x a hay)).deduction.empty,
    (r.generalizeSingleton x (universalVacuity x y b hbx)).deduction.empty⟩

#print axioms universalSpecializeNeighborhood
#print axioms Context.generalizeSingleton
#print axioms universalAlphaNeighborhood
end M6.PA.ActualCertificateEquivalence

