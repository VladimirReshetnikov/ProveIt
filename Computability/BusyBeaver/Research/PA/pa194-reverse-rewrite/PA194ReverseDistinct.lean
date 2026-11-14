import PA194NegativeSpecialization
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194Logic
abbrev MembershipSlot := PA194ReverseSeeds.MembershipSlot
abbrev chi := PA194ReverseSeeds.chi

def chiDirect (k : MembershipSlot) (d a b : Nat) :
    Derivation (wim (weq a b) (wim (chi k d a) (chi k d b))) := by
  cases k with
  | first => exact memLeft a b d
  | second => exact memRight a b d
  | diagonal =>
    let he : Context [wel a a,weq a b] (weq a b) := .assumption (by simp)
    let hm : Context [wel a a,weq a b] (wel a a) := .assumption (by simp)
    let hm' := Context.mp hm (.mp he (.closed (memLeft a b a)))
    exact (Context.mp hm' (.mp he (.closed (memRight a b b)))).deduction.deduction.empty

def chiVacuity (k : MembershipSlot) (d t y : Nat)
    (hyt : y ≠ t) (hyd : k = .diagonal ∨ y ≠ d) :
    Derivation (wim (chi k d t) (wal y (chi k d t))) := by
  cases k with
  | first => exact membershipVacuity t d y hyt (hyd.resolve_left (by decide))
  | second => exact membershipVacuity d t y (hyd.resolve_left (by decide)) hyt
  | diagonal => exact membershipVacuity t t y hyt hyt

def Context.negImpLeft {Γ : List Nat} {a b : Nat} (p : Context Γ (wn (wim a b))) : Context Γ a := by
  let ha : Context (a :: wn a :: Γ) a := .assumption (by simp)
  let hn : Context (a :: wn a :: Γ) (wn a) := .assumption (by simp)
  let hi : Context (wn a :: Γ) (wim a b) := ((Context.mp ha hn).explosion b).deduction
  exact (Context.mp hi (p.up (wn a))).deduction.dne

def Context.negImpRight {Γ : List Nat} {a b : Nat} (p : Context Γ (wn (wim a b))) : Context Γ (wn b) := by
  let hb : Context (b :: Γ) b := .assumption (by simp)
  exact (Context.mp (hb.lift a) (p.up b)).deduction

def phiToEquality (e q p : Nat) : Derivation (wim (wn (wim e (wim q p))) e) := by
  let h : Context [wn (wim e (wim q p))] (wn (wim e (wim q p))) := .assumption (by simp)
  exact h.negImpLeft.deduction.empty

def phiToQ (e q p : Nat) : Derivation (wim (wn (wim e (wim q p))) q) := by
  let h : Context [wn (wim e (wim q p))] (wn (wim e (wim q p))) := .assumption (by simp)
  exact h.negImpRight.negImpLeft.deduction.empty

def phiToNotP (e q p : Nat) : Derivation (wim (wn (wim e (wim q p))) (wn p)) := by
  let h : Context [wn (wim e (wim q p))] (wn (wim e (wim q p))) := .assumption (by simp)
  exact h.negImpRight.negImpRight.deduction.empty

/-- Reverse membership rewriting when the fixed parameter is fresh at `a`.
The diagonal slot has no fixed-parameter restriction. -/
def reverseDistinct (k : MembershipSlot) (d a b : Nat)
    (hab : a ≠ b) (had : k = .diagonal ∨ a ≠ d) :
    Derivation (wim (weq a b) (wim (chi k d b) (chi k d a))) := by
  let e := weq a b
  let p := chi k d a
  let q := chi k d b
  let C := wim e (wim q p)
  let φ := wn C
  let P := point a a φ
  let A := wim (wel a a) P
  let B := wim (wel φ a) φ
  let S := wal a (wa A B)
  have hφa : φ ≠ a := by
    have hf := (PA194ReverseSeeds.separator_fresh_labels k d a b).1
    change a < φ at hf
    omega
  have hca : a ≠ φ := Ne.symm hφa
  have hp : Derivation (wim φ (wn p)) := phiToNotP e q p
  let hconj : Context [wa A B] (wa A B) := .assumption (by simp)
  have hproj : Derivation (wim (wa A B) B) := hconj.andRight.deduction.empty
  have hS : Derivation (wim S (wal a (wim (wel φ a) (wn p)))) :=
    implicationCompose (liftImp a hproj)
      (liftImp a (Dominated.lift_right φ (wn p) hp (wel φ a)))
  have hspec : Derivation (wim (wal a (wim (wel φ a) (wn p)))
      (wim (wel φ b) (wn q))) :=
    negativeSpecialization a b φ p q hca hab (chiDirect k d b a) (chiVacuity k d b a hab had)
  have hSQ : Derivation (wim S (wim (wel φ b) (wn q))) := implicationCompose hS hspec
  let hpCtx : Context [P,S,φ] P := .assumption (by simp)
  let hsCtx : Context [P,S,φ] S := .assumption (by simp)
  let hφCtx : Context [P,S,φ] φ := .assumption (by simp)
  let heCtx : Context [P,S,φ] e := .mp hφCtx (.closed (phiToEquality e q p))
  let hqCtx : Context [P,S,φ] q := .mp hφCtx (.closed (phiToQ e q p))
  let hMa : Context [P,S,φ] (wel φ a) := .mp hφCtx hpCtx
  let hMb : Context [P,S,φ] (wel φ b) := .mp hMa (.mp heCtx (.closed (memRight a b φ)))
  let hnq : Context [P,S,φ] (wn q) := .mp hMb (.mp hsCtx (.closed hSQ))
  have himp : Derivation (wim φ (wim S (wn P))) :=
    (Context.mp hqCtx hnq).deduction.deduction.deduction.empty
  have hAll : Derivation (wim (wal φ φ) (wal φ (wim S (wn P)))) :=
    .mp (.all φ himp) (r2 φ φ (wim S (wn P)))
  have hdiag : Derivation (wim φ (wal φ φ)) := .diagonal φ
  have hφQ : Derivation (wim φ (qGate a a φ)) := implicationCompose hdiag hAll
  have hnQ : Derivation (wn (qGate a a φ)) := pointedSeparation a a φ hφa hφa
  have hnnC : Derivation (wn (wn C)) := implicationCompose hφQ hnQ
  exact .mp hnnC (doubleNegationElimination C)

/-- Uniform reverse membership rewriting, including all label collisions. -/
def reverseAll (k : MembershipSlot) (d a b : Nat) :
    Derivation (wim (weq a b) (wim (chi k d b) (chi k d a))) := by
  by_cases hab : a = b
  · subst b
    exact PA194ReverseSeeds.equalLabelReverse k d a
  · by_cases had : a = d
    · subst d
      cases k with
      | diagonal => exact reverseDistinct .diagonal a a b hab (Or.inl rfl)
      | first =>
        let he : Context [wel b a,weq a b] (weq a b) := .assumption (by simp)
        let hm : Context [wel b a,weq a b] (wel b a) := .assumption (by simp)
        let hbb : Context [wel b a,weq a b] (wel b b) :=
          .mp hm (.mp he (.closed (memRight a b b)))
        let haa : Context [wel b a,weq a b] (wel a a) :=
          .mp hbb (.mp he (.closed (reverseDistinct .diagonal a a b hab (Or.inl rfl))))
        exact haa.deduction.deduction.empty
      | second =>
        let he : Context [wel a b,weq a b] (weq a b) := .assumption (by simp)
        let hm : Context [wel a b,weq a b] (wel a b) := .assumption (by simp)
        let hbb : Context [wel a b,weq a b] (wel b b) :=
          .mp hm (.mp he (.closed (memLeft a b b)))
        let haa : Context [wel a b,weq a b] (wel a a) :=
          .mp hbb (.mp he (.closed (reverseDistinct .diagonal a a b hab (Or.inl rfl))))
        exact haa.deduction.deduction.empty
    · exact reverseDistinct k d a b hab (Or.inr had)

#print axioms reverseAll
#print axioms reverseDistinct
#print axioms chiDirect
#print axioms chiVacuity
#print axioms phiToEquality
#print axioms phiToQ
#print axioms phiToNotP
end PA194Logic
