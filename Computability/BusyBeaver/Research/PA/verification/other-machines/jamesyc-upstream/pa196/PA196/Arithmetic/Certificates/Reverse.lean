module
public import PA196.Arithmetic.Certificates.Vacuity
@[expose] public section

/-! Uniform reverse membership rewriting from guarded equality vacuity.
This is the new argument in `paper/pa196.tex`, including the collision case
where a variable label equals the first negative-property code.
-/
open M6.PA
namespace PA196.Arithmetic.Certificates.Logic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open Checker HeadGraphs
universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]


noncomputable def specializeWithMirroredEquality (z c atom target : V)
    (hv : Certificate (wim target (wal z target)))
    (hr : Certificate (wim (weq c z) (wim atom target))) :
    Certificate (wim (wal z atom) target) := by
  classical
  let hs : Certificate (wim atom (wim (weq c z) target)) :=
    .mp hr (Dominated.exchange (weq c z) atom target)
  let hu : Context [wal z atom] (wal z atom) := .assumption (by simp)
  let ht : Context [wal z atom] (wal z (wim (weq c z) target)) :=
    hu.forallMP z (.closed (.all z hs))
  exact (Context.existsElim z hv ht (.closed (r1 z c))).deduction.empty

/-- Specialization of a negative membership property needs direct rewriting only. -/
noncomputable def negativeSpecialization (y v c p q : V) (hcy : y ≠ c) (hvy : y ≠ v)
    (hr : Certificate (wim (weq v y) (wim q p)))
    (hv : Certificate (wim q (wal y q))) :
    Certificate (wim (wal y (wim (wel c y) (wn p))) (wim (wel c v) (wn q))) := by
  classical
  let e := weq v y
  let py := wim (wel c y) (wn p)
  let he : Context [q,wel c v,py,e] e := .assumption (by simp)
  let hq : Context [q,wel c v,py,e] q := .assumption (by simp)
  let hm : Context [q,wel c v,py,e] (wel c v) := .assumption (by simp)
  let hy : Context [q,wel c v,py,e] py := .assumption (by simp)
  let hmy := Context.mp hm (.mp he (.closed (memRight v y c)))
  let hp := Context.mp hq (.mp he (.closed hr))
  let contra := Context.mp hp (.mp hmy hy)
  let hh : Certificate (wim e (wim py (wim (wel c v) (wn q)))) :=
    contra.deduction.deduction.deduction.deduction.empty
  exact specializeWithMirroredEquality y v py (wim (wel c v) (wn q))
    (implicationVacuity y _ _ (membershipVacuity c v y hcy hvy)
      (negationVacuity y q hv)) hh

noncomputable def doubleNegationIntroduction (a : V) : Certificate (wim a (wn (wn a))) := by
  classical
  let hp : Context [wn a,a] a := .assumption (by simp)
  let hn : Context [wn a,a] (wn a) := .assumption (by simp)
  exact (Context.mp hp hn).deduction.deduction.empty

/-- One bounded branch suffices; no unbounded search for a fresh code occurs. -/
noncomputable def propertyCode (p b : V) : V := by
  classical
  exact if wn p = b then wn (wn (wn p)) else wn p

theorem propertyCode_gt (p b : V) : p < propertyCode p b := by
  classical
  have h1 := wn_strict p
  have h2 := wn_strict (wn p)
  have h3 := wn_strict (wn (wn p))
  unfold propertyCode
  split
  · exact lt_trans h1 (lt_trans h2 h3)
  · exact h1

theorem propertyCode_ne (p b : V) : propertyCode p b ≠ b := by
  classical
  have h2 := wn_strict (wn p)
  have h3 := wn_strict (wn (wn p))
  unfold propertyCode
  split
  · rename_i he
    rw [← he]
    exact ne_of_gt (lt_trans h2 h3)
  · assumption

noncomputable def propertyToNegative (p b : V) : Certificate (wim (propertyCode p b) (wn p)) := by
  classical
  unfold propertyCode
  split
  · exact doubleNegationElimination (wn p)
  · exact identity (wn p)

noncomputable def negativeToProperty (p b : V) : Certificate (wim (wn p) (propertyCode p b)) := by
  classical
  unfold propertyCode
  split
  · exact doubleNegationIntroduction (wn p)
  · exact identity (wn p)

/-- Core separation argument. All supplied premises are finite derivations;
the three concrete membership families below discharge them. -/
noncomputable def reverseFromProperty (a b c p q : V) (hca : c ≠ a) (hab : a ≠ b)
    (hr : Certificate (wim (weq b a) (wim q p)))
    (hqv : Certificate (wim q (wal a q)))
    (hcn : Certificate (wim c (wn p)))
    (hnc : Certificate (wim (wn p) c))
    (hcv : Certificate (wim (wim (weq a b) (wim q p))
      (wal c (wim (weq a b) (wim q p))))) :
    Certificate (wim (weq a b) (wim q p)) := by
  classical
  let S := separation a a c
  let P := point a a c
  let C := wim (weq a b) (wim q p)
  let A := wim (wel a a) P
  let B := wim (wel c a) c
  let hs : Context [wa A B] (wa A B) := .assumption (by simp)
  let base : Certificate (wim (wa A B) (wim (wel c a) (wn p))) :=
    (hs.andRight.arrowCompose (.closed hcn)).deduction.empty
  let hS : Certificate (wim S (wim (wel c b) (wn q))) :=
    implicationCompose (liftImp a base)
      (negativeSpecialization a b c p q (Ne.symm hca) hab hr hqv)
  let hn : Context [wn p,q,weq a b,P,S] (wn p) := .assumption (by simp)
  let hqq : Context [wn p,q,weq a b,P,S] q := .assumption (by simp)
  let he : Context [wn p,q,weq a b,P,S] (weq a b) := .assumption (by simp)
  let hP : Context [wn p,q,weq a b,P,S] P := .assumption (by simp)
  let hSS : Context [wn p,q,weq a b,P,S] S := .assumption (by simp)
  let hm := Context.mp (.mp hn (.closed hnc)) hP
  let hm' := Context.mp hm (.mp he (.closed (memRight a b c)))
  let nq := Context.mp hm' (.mp hSS (.closed hS))
  let concl : Certificate (wim S (wim P C)) :=
    (Context.mp hqq nq).deduction.dne.deduction.deduction.deduction.deduction.empty
  let hPP : Context [P,S,wn C] P := .assumption (by simp)
  let hSS' : Context [P,S,wn C] S := .assumption (by simp)
  let hnC : Context [P,S,wn C] (wn C) := .assumption (by simp)
  let hCC := Context.mp hPP (.mp hSS' (.closed concl))
  let lifted : Certificate (wim (wn C) (wal c (wim S (wn P)))) :=
    implicationCompose (negationVacuity c C hcv)
      (liftImp c (Context.mp hCC hnC).deduction.deduction.deduction.empty)
  exact .mp (.mp (pointedSeparation a a c hca hca) (contrapose lifted))
    (doubleNegationElimination C)

inductive MembershipSlot where
  | first | second | diagonal
  deriving DecidableEq

noncomputable def chi : MembershipSlot → V → V → V
  | .first,d,t => wel t d
  | .second,d,t => wel d t
  | .diagonal,_,t => wel t t

noncomputable def chiDirect (k : MembershipSlot) (d a b : V) :
    Certificate (wim (weq a b) (wim (chi k d a) (chi k d b))) := by
  classical
  cases k with
  | first => exact memLeft a b d
  | second => exact memRight a b d
  | diagonal =>
    let he : Context [wel a a,weq a b] (weq a b) := .assumption (by simp)
    let hm : Context [wel a a,weq a b] (wel a a) := .assumption (by simp)
    let hm' := Context.mp hm (.mp he (.closed (memLeft a b a)))
    exact (Context.mp hm' (.mp he (.closed (memRight a b b)))).deduction.deduction.empty

noncomputable def chiVacuity (k : MembershipSlot) (d t y : V)
    (hyt : y ≠ t) (hyd : k = .diagonal ∨ y ≠ d) :
    Certificate (wim (chi k d t) (wal y (chi k d t))) := by
  classical
  cases k with
  | first => exact membershipVacuity t d y hyt (hyd.resolve_left (by decide))
  | second => exact membershipVacuity d t y (hyd.resolve_left (by decide)) hyt
  | diagonal => exact membershipVacuity t t y hyt hyt

theorem chi_fresh (k : MembershipSlot) (d a c : V) (h : chi k d a < c) :
    c ≠ a ∧ (k = .diagonal ∨ c ≠ d) := by
  cases k with
  | first =>
    have h' := wel_bounds a d
    exact ⟨ne_of_gt (lt_trans h'.1 h),Or.inr (ne_of_gt (lt_trans h'.2 h))⟩
  | second =>
    have h' := wel_bounds d a
    exact ⟨ne_of_gt (lt_trans h'.2 h),Or.inr (ne_of_gt (lt_trans h'.1 h))⟩
  | diagonal =>
    have h' := wel_bounds a a
    exact ⟨ne_of_gt (lt_trans h'.1 h),Or.inl rfl⟩

/-- The only side condition is that the fixed label is foreign to `a`;
the diagonal family has no fixed label. -/
noncomputable def reverseChi (k : MembershipSlot) (d a b : V) (hab : a ≠ b)
    (hda : k = .diagonal ∨ a ≠ d) :
    Certificate (wim (weq a b) (wim (chi k d b) (chi k d a))) := by
  classical
  let p := chi k d a
  let q := chi k d b
  let c := propertyCode p b
  have fresh := chi_fresh k d a c (propertyCode_gt p b)
  have hcb : c ≠ b := propertyCode_ne p b
  exact reverseFromProperty a b c p q fresh.1 hab
    (chiDirect k d b a) (chiVacuity k d b a hab hda)
    (propertyToNegative p b) (negativeToProperty p b)
    (implicationVacuity c _ _ (equalityVacuity a b c fresh.1 hcb)
      (implicationVacuity c q p
        (chiVacuity k d b c hcb fresh.2) (chiVacuity k d a c fresh.1 fresh.2)))

/-- Reverse rewriting of the second membership argument, for every label coincidence. -/
noncomputable def reverseRight (a b d : V) :
    Certificate (wim (weq a b) (wim (wel d b) (wel d a))) := by
  classical
  by_cases hab : a = b
  · subst b
    exact .mp (identity (wel d a)) (Dominated.k _ (weq a a))
  · by_cases had : a = d
    · subst d
      let he : Context [wel a b,weq a b] (weq a b) := .assumption (by simp)
      let hm : Context [wel a b,weq a b] (wel a b) := .assumption (by simp)
      let hm' := Context.mp hm (.mp he (.closed (memLeft a b b)))
      exact (Context.mp hm' (.mp he (.closed
        (reverseChi .diagonal 0 a b hab (Or.inl rfl))))).deduction.deduction.empty
    · exact reverseChi .second d a b hab (Or.inr had)

/-- Reverse rewriting of the first membership argument, for every label coincidence. -/
noncomputable def reverseLeft (a b d : V) :
    Certificate (wim (weq a b) (wim (wel b d) (wel a d))) := by
  classical
  by_cases hab : a = b
  · subst b
    exact .mp (identity (wel a d)) (Dominated.k _ (weq a a))
  · by_cases had : a = d
    · subst d
      let he : Context [wel b a,weq a b] (weq a b) := .assumption (by simp)
      let hm : Context [wel b a,weq a b] (wel b a) := .assumption (by simp)
      let hm' := Context.mp hm (.mp he (.closed (memRight a b b)))
      exact (Context.mp hm' (.mp he (.closed
        (reverseChi .diagonal 0 a b hab (Or.inl rfl))))).deduction.deduction.empty
    · exact reverseChi .first d a b hab (Or.inr had)

#print axioms negativeSpecialization
#print axioms propertyCode_ne
#print axioms reverseRight
#print axioms reverseLeft
end PA196.Arithmetic.Certificates.Logic
