module
public import M6PA.Theory
public import M6PA.Calibration.ActualBasisLogic
@[expose] public section
/-! Modal closure in the literal actual basis and an explicit equality-free
replacement formula testcase. No primitive equality vacuity is used. -/
namespace M6.PA.NativeCalculus.ActualBasis

def negationVacuity (x a : Nat) (hv : Proof (wim a (wal x a))) :
    Proof (wim (wn a) (wal x (wn a))) := by
  let hc := contrapose hv
  let hg := Proof.all x hc
  let hl := Proof.mp hg (r2 x (wn (wal x a)) (wn a))
  let hr := contrapose (r6 x a)
  let hf := implicationCompose hr (doubleNegationElimination (wal x (wn (wal x a))))
  exact implicationCompose hf hl


def r4 (a b c : Nat) : Proof (rho4 a b c) := by
  simpa only [M6.Source.ActualAXCode.rho4,M6.Source.AXCode.rho4,
    M6.Source.AXCode.wim,M6.Source.AXCode.wal,rho4,wim,wal] using Proof.r4 a b c

def Context.casesOnFormula {Γ : List Nat} (a : Nat) {c : Nat}
    (p : Context (a :: Γ) c) (q : Context (wn a :: Γ) c) : Context Γ c := by
  let hn : Context (wn c :: Γ) (wn c) := .assumption (by simp)
  let hp : Context (wn c :: Γ) (wim a c) := p.deduction.up (wn c)
  let hna : Context (wn c :: Γ) (wn a) :=
    .mp hn (.mp hp (.closed (contraposition a c)))
  let hc : Context (wn c :: Γ) c := .mp hna (q.deduction.up (wn c))
  exact (Context.mp hc hn).deduction.dne

def implicationVacuity (x a b : Nat)
    (ha : Proof (wim a (wal x a))) (hb : Proof (wim b (wal x b))) :
    Proof (wim (wim a b) (wal x (wim a b))) := by
  let c := wal x (wim a b)
  let hbLift : Proof (wim b c) := implicationCompose hb
    (.mp (.all x (Dominated.k b a)) (r2 x b (wim a b)))
  let hn : Context [a, wn a] (wn a) := .assumption (by simp)
  let hp : Context [a, wn a] a := .assumption (by simp)
  let hnot : Proof (wim (wn a) (wim a b)) :=
    ((Context.mp hp hn).explosion b).deduction.deduction.empty
  let haLift : Proof (wim (wn a) c) := implicationCompose (negationVacuity x a ha)
    (.mp (.all x hnot) (r2 x (wn a) (wim a b)))
  let pa : Context [a, wim a b] a := .assumption (by simp)
  let pab : Context [a, wim a b] (wim a b) := .assumption (by simp)
  let pc : Context [a, wim a b] c := .mp (.mp pa pab) (.closed hbLift)
  let pna : Context [wn a, wim a b] (wn a) := .assumption (by simp)
  let pnc : Context [wn a, wim a b] c := .mp pna (.closed haLift)
  exact (Context.casesOnFormula a pc pnc).deduction.empty

def universalVacuity (x y a : Nat) (h : Proof (wim a (wal x a))) :
    Proof (wim (wal y a) (wal x (wal y a))) :=
  implicationCompose (.mp (.all y h) (r2 y a (wal x a))) (r4 y x a)


def conjunctionVacuity (x a b : Nat)
    (ha : Proof (wim a (wal x a))) (hb : Proof (wim b (wal x b))) :
    Proof (wim (wa a b) (wal x (wa a b))) :=
  negationVacuity x (wim a (wn b))
    (implicationVacuity x a (wn b) ha (negationVacuity x b hb))

def iffCode (a b : Nat) := wa (wim a b) (wim b a)
def neighborhoodEquality (a b z : Nat) :=
  wa (wal z (iffCode (wel a z) (wel b z)))
     (wal z (iffCode (wel z a) (wel z b)))

def iffVacuity (x a b : Nat)
    (ha : Proof (wim a (wal x a))) (hb : Proof (wim b (wal x b))) :
    Proof (wim (iffCode a b) (wal x (iffCode a b))) :=
  conjunctionVacuity x _ _ (implicationVacuity x a b ha hb)
    (implicationVacuity x b a hb ha)

/-- Concrete fresh-variable quantifier case for the two-neighborhood equality
replacement. This is not primitive equality, nor a completed PA translation. -/
def neighborhoodEqualityVacuity (a b z c : Nat)
    (ha : c ≠ a) (hb : c ≠ b) (hz : c ≠ z) :
    Proof (wim (neighborhoodEquality a b z)
      (wal c (neighborhoodEquality a b z))) :=
  conjunctionVacuity c _ _
    (universalVacuity c z _ (iffVacuity c _ _
      (membershipVacuity a z c ha hz) (membershipVacuity b z c hb hz)))
    (universalVacuity c z _ (iffVacuity c _ _
      (membershipVacuity z a c hz ha) (membershipVacuity z b c hz hb)))

#print axioms neighborhoodEqualityVacuity
end M6.PA.NativeCalculus.ActualBasis
