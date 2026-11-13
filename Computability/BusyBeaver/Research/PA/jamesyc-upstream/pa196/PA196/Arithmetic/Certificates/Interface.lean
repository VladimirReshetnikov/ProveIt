module
public import PA196.Arithmetic.Certificates.Neighborhood
@[expose] public section
open M6.PA
namespace PA196.Arithmetic.Certificates.Logic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open Checker HeadGraphs
universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

/-! A compact relational-interpretation boundary. All equality facts below
concern the defined neighborhood relation. Primitive symmetry is unnecessary.
-/
noncomputable abbrev neighborhoodEquality (a b z : V) : V := neighborhood a b z

/- These aliases retain the two historical forward membership-rewrite types.
No corresponding alias is asserted for historical primitive equality R7. -/
noncomputable abbrev r3 (a b c : V) := memRight a b c
noncomputable abbrev r5 (a b c : V) := memLeft c a b

theorem wel_left_lt (a b : V) : a < wel a b := (wel_bounds a b).1
theorem wel_right_lt (a b : V) : b < wel a b := (wel_bounds a b).2

noncomputable def negatedImplicationLeft (a b : V) : Certificate (wim (wn (wim a b)) a) := by
  let hp : Context [a,wn a,wn (wim a b)] a := .assumption (by simp)
  let hn : Context [a,wn a,wn (wim a b)] (wn a) := .assumption (by simp)
  let hab : Context [wn a,wn (wim a b)] (wim a b) :=
    ((Context.mp hp hn).explosion b).deduction
  let hnot : Context [wn a,wn (wim a b)] (wn (wim a b)) := .assumption (by simp)
  exact (Context.mp hab hnot).deduction.dne.deduction.empty

noncomputable def iffReflexive (a : V) : Certificate (iffCode a a) :=
  (Context.andIntro (.closed (identity a)) (.closed (identity a))).empty

noncomputable def iffTransitivity (a b c : V) :
    Certificate (wim (iffCode a b) (wim (iffCode b c) (iffCode a c))) := by
  let p : Context [iffCode b c,iffCode a b] (wa (wim a b) (wim b a)) :=
    .assumption (by simp [iffCode])
  let q : Context [iffCode b c,iffCode a b] (wa (wim b c) (wim c b)) :=
    .assumption (by simp [iffCode])
  exact (Context.andIntro (p.andLeft.arrowCompose q.andLeft)
    (q.andRight.arrowCompose p.andRight)).deduction.deduction.empty

noncomputable def neighborhoodReflexivityCore (a z : V) : Certificate (neighborhoodEquality a a z) :=
  (Context.andIntro (.closed (.all z (iffReflexive (wel a z))))
    (.closed (.all z (iffReflexive (wel z a))))).empty

noncomputable abbrev neighborhoodSymmetryCore (a b z : V) := neighborhoodSymmetry a b z

noncomputable def neighborhoodTransitivityCore (a b c z : V) :
    Certificate (wim (neighborhoodEquality a b z)
      (wim (neighborhoodEquality b c z) (neighborhoodEquality a c z))) := by
  let p : Context [neighborhoodEquality b c z,neighborhoodEquality a b z]
      (neighborhoodEquality a b z) := .assumption (by simp)
  let q : Context [neighborhoodEquality b c z,neighborhoodEquality a b z]
      (neighborhoodEquality b c z) := .assumption (by simp)
  let l := q.andLeft.forallMP z (p.andLeft.forallMP z
    (.closed (.all z (iffTransitivity (wel a z) (wel b z) (wel c z)))))
  let r := q.andRight.forallMP z (p.andRight.forallMP z
    (.closed (.all z (iffTransitivity (wel z a) (wel z b) (wel z c)))))
  exact (Context.andIntro l r).deduction.deduction.empty

noncomputable def iffVacuity (x a b : V)
    (ha : Certificate (wim a (wal x a))) (hb : Certificate (wim b (wal x b))) :
    Certificate (wim (iffCode a b) (wal x (iffCode a b))) :=
  conjunctionVacuity x _ _ (implicationVacuity x a b ha hb)
    (implicationVacuity x b a hb ha)

noncomputable def neighborhoodEqualityVacuity (a b z c : V)
    (ha : c ≠ a) (hb : c ≠ b) (hz : c ≠ z) :
    Certificate (wim (neighborhoodEquality a b z) (wal c (neighborhoodEquality a b z))) :=
  conjunctionVacuity c _ _
    (universalVacuity c z _ (iffVacuity c _ _
      (membershipVacuity a z c ha hz) (membershipVacuity b z c hb hz)))
    (universalVacuity c z _ (iffVacuity c _ _
      (membershipVacuity z a c hz ha) (membershipVacuity z b c hz hb)))

noncomputable def implicationRewriteSame (e p q p' q' : V)
    (hp : Certificate (wim e (wim p' p)))
    (hq : Certificate (wim e (wim q q'))) :
    Certificate (wim e (wim (wim p q) (wim p' q'))) := by
  let he : Context [p',wim p q,e] e := .assumption (by simp)
  let hpp : Context [p',wim p q,e] p' := .assumption (by simp)
  let hi : Context [p',wim p q,e] (wim p q) := .assumption (by simp)
  let hpa : Context [p',wim p q,e] p := .mp hpp (.mp he (.closed hp))
  exact (Context.mp (.mp hpa hi) (.mp he (.closed hq))).deduction.deduction.deduction.empty

noncomputable def universalMembershipImplicationRight (a b z c : V)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    Certificate (wim (wal z (wim (wel a z) (wel b z))) (wim (wel a c) (wel b c))) :=
  specializeWithMirroredEquality z c _ _
    (implicationVacuity z _ _ (membershipVacuity a c z hza hzc)
      (membershipVacuity b c z hzb hzc))
    (implicationRewriteSame (weq c z) _ _ _ _ (memRight c z a) (reverseRight c z b))

noncomputable def universalMembershipImplicationLeft (a b z c : V)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    Certificate (wim (wal z (wim (wel z a) (wel z b))) (wim (wel c a) (wel c b))) :=
  specializeWithMirroredEquality z c _ _
    (implicationVacuity z _ _ (membershipVacuity c a z hzc hza)
      (membershipVacuity c b z hzc hzb))
    (implicationRewriteSame (weq c z) _ _ _ _ (memLeft c z a) (reverseLeft c z b))

noncomputable def forallIffForward (z p q : V) :
    Certificate (wim (wal z (iffCode p q)) (wal z (wim p q))) := by
  let hp : Context [iffCode p q] (wa (wim p q) (wim q p)) := .assumption (by simp [iffCode])
  let proj : Certificate (wim (iffCode p q) (wim p q)) := hp.andLeft.deduction.empty
  exact .mp (.all z proj) (r2 z _ _)

noncomputable def neighborhoodRightCongruenceCore (a b z c : V)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    Certificate (wim (neighborhoodEquality a b z) (wim (wel a c) (wel b c))) := by
  let h : Context [neighborhoodEquality a b z] (neighborhoodEquality a b z) := .assumption (by simp)
  let hi := Context.mp h.andLeft (.closed (forallIffForward z (wel a z) (wel b z)))
  exact (Context.mp hi (.closed (universalMembershipImplicationRight a b z c hza hzb hzc))).deduction.empty

noncomputable def neighborhoodLeftCongruenceCore (a b z c : V)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) :
    Certificate (wim (neighborhoodEquality a b z) (wim (wel c a) (wel c b))) := by
  let h : Context [neighborhoodEquality a b z] (neighborhoodEquality a b z) := .assumption (by simp)
  let hi := Context.mp h.andRight (.closed (forallIffForward z (wel z a) (wel z b)))
  exact (Context.mp hi (.closed (universalMembershipImplicationLeft a b z c hza hzb hzc))).deduction.empty

noncomputable def neighborhoodBinderChangeCore (a b z z' : V)
    (hza : z ≠ a) (hzb : z ≠ b) (hna : z' ≠ a) (hnb : z' ≠ b) :
    Certificate (wim (neighborhoodEquality a b z) (neighborhoodEquality a b z')) := by
  classical
  by_cases he : z' = z
  · subst z'; exact identity _
  have hnz : z ≠ z' := Ne.symm he
  let h : Context [neighborhoodEquality a b z] (neighborhoodEquality a b z) := .assumption (by simp)
  let hs := Context.mp h (.closed (neighborhoodSymmetry a b z))
  let l := Context.andIntro
    (.mp h (.closed (neighborhoodRightCongruenceCore a b z z' hza hzb hnz)))
    (.mp hs (.closed (neighborhoodRightCongruenceCore b a z z' hzb hza hnz)))
  let r := Context.andIntro
    (.mp h (.closed (neighborhoodLeftCongruenceCore a b z z' hza hzb hnz)))
    (.mp hs (.closed (neighborhoodLeftCongruenceCore b a z z' hzb hza hnz)))
  have hv : ∀ f, f ∈ [neighborhoodEquality a b z] → Certificate (wim f (wal z' f)) := by
    intro f hf
    have hf' : f = neighborhoodEquality a b z := List.mem_singleton.mp hf
    subst f
    exact neighborhoodEqualityVacuity a b z z' hna hnb he
  exact (Context.andIntro (l.generalize z' hv) (r.generalize z' hv)).deduction.empty

noncomputable def universalSpecializeNeighborhoodCore (x y z a b : V)
    (hzx : z ≠ x) (hzy : z ≠ y)
    (hr : Certificate (wim (neighborhoodEquality x y z) (wim a b)))
    (hv : Certificate (wim b (wal x b))) : Certificate (wim (wal x a) b) := by
  let e := neighborhoodEquality x y z
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

noncomputable def universalAlphaNeighborhoodCore (x y z a b : V)
    (hzx : z ≠ x) (hzy : z ≠ y)
    (hf : Certificate (wim (neighborhoodEquality x y z) (wim a b)))
    (hb : Certificate (wim (neighborhoodEquality x y z) (wim b a)))
    (hbx : Certificate (wim b (wal x b))) (hay : Certificate (wim a (wal y a))) :
    Certificate (wim (wal x a) (wal y b)) × Certificate (wim (wal y b) (wal x a)) := by
  let f : Context [wal x a] b := .mp (.assumption (by simp))
    (.closed (universalSpecializeNeighborhoodCore x y z a b hzx hzy hf hbx))
  let hreverse := implicationCompose (neighborhoodSymmetry y x z) hb
  let r : Context [wal y b] a := .mp (.assumption (by simp))
    (.closed (universalSpecializeNeighborhoodCore y x z b a hzy hzx hreverse hay))
  exact ⟨(f.generalizeSingleton y (universalVacuity y x a hay)).deduction.empty,
    (r.generalizeSingleton x (universalVacuity x y b hbx)).deduction.empty⟩

#print axioms neighborhoodRightCongruenceCore
#print axioms neighborhoodLeftCongruenceCore
#print axioms neighborhoodBinderChangeCore
end PA196.Arithmetic.Certificates.Logic
