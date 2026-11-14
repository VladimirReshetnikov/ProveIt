import PA194LogicConnectives
import PA194ReverseSeeds

/-! Extraction of the new guarded gate and finite modal proof recipes.
Every construction returns a derivation from `the PA194 derivation rules`'s rules.
-/
namespace PA194Logic

def negImpLeft {a b : Nat} (g : Derivation (wn (wim a b))) : Derivation a := by
  let ha : Context [a,wn a] a := .assumption (by simp)
  let hn : Context [a,wn a] (wn a) := .assumption (by simp)
  let hi : Context [wn a] (wim a b) := ((Context.mp ha hn).explosion b).deduction
  exact (Context.mp hi (.closed g)).deduction.dne.empty

def negImpRight {a b : Nat} (g : Derivation (wn (wim a b))) : Derivation (wn b) := by
  let hb : Context [b] b := .assumption (by simp)
  exact (Context.mp (hb.lift a) (.closed g)).deduction.empty

def membershipVacuity (a b c : Nat) (hca : c ≠ a) (hcb : c ≠ b) :
    Derivation (wim (wel a b) (wal c (wel a b))) :=
  PA194ReverseSeeds.membershipVacuity a b c hca hcb

def pointedSeparation (a b c : Nat) (hca : c ≠ a) (hcb : c ≠ b) :
    Derivation (wn (qGate a b c)) :=
  PA194ReverseSeeds.notSeparationTail a b c hca hcb

def negationVacuity (x a : Nat) (hv : Derivation (wim a (wal x a))) :
    Derivation (wim (wn a) (wal x (wn a))) := by
  let hc := contrapose hv
  let hg := PA194DerivationCompiler.Derivation.all x hc
  let hl := PA194DerivationCompiler.Derivation.mp hg (r2 x (wn (wal x a)) (wn a))
  let hr := contrapose (r6 x a)
  let hf := implicationCompose hr (doubleNegationElimination (wal x (wn (wal x a))))
  exact implicationCompose hf hl

def Context.casesOnFormula {Γ : List Nat} (a : Nat) {c : Nat}
    (p : Context (a :: Γ) c) (q : Context (wn a :: Γ) c) : Context Γ c := by
  let hn : Context (wn c :: Γ) (wn c) := .assumption (by simp)
  let hp : Context (wn c :: Γ) (wim a c) := p.deduction.up (wn c)
  let hna : Context (wn c :: Γ) (wn a) :=
    .mp hn (.mp hp (.closed (contraposition a c)))
  let hc : Context (wn c :: Γ) c := .mp hna (q.deduction.up (wn c))
  exact (Context.mp hc hn).deduction.dne

def implicationVacuity (x a b : Nat)
    (ha : Derivation (wim a (wal x a))) (hb : Derivation (wim b (wal x b))) :
    Derivation (wim (wim a b) (wal x (wim a b))) := by
  let c := wal x (wim a b)
  let hbLift : Derivation (wim b c) := implicationCompose hb
    (.mp (.all x (Dominated.k b a)) (r2 x b (wim a b)))
  let hn : Context [a,wn a] (wn a) := .assumption (by simp)
  let hp : Context [a,wn a] a := .assumption (by simp)
  let hnot : Derivation (wim (wn a) (wim a b)) :=
    ((Context.mp hp hn).explosion b).deduction.deduction.empty
  let haLift : Derivation (wim (wn a) c) := implicationCompose (negationVacuity x a ha)
    (.mp (.all x hnot) (r2 x (wn a) (wim a b)))
  let pa : Context [a,wim a b] a := .assumption (by simp)
  let pab : Context [a,wim a b] (wim a b) := .assumption (by simp)
  let pc : Context [a,wim a b] c := .mp (.mp pa pab) (.closed hbLift)
  let pna : Context [wn a,wim a b] (wn a) := .assumption (by simp)
  let pnc : Context [wn a,wim a b] c := .mp pna (.closed haLift)
  exact (Context.casesOnFormula a pc pnc).deduction.empty

def universalVacuity (x y a : Nat) (h : Derivation (wim a (wal x a))) :
    Derivation (wim (wal y a) (wal x (wal y a))) :=
  implicationCompose (.mp (.all y h) (r2 y a (wal x a))) (r4 y x a)

def conjunctionVacuity (x a b : Nat)
    (ha : Derivation (wim a (wal x a))) (hb : Derivation (wim b (wal x b))) :
    Derivation (wim (wa a b) (wal x (wa a b))) :=
  negationVacuity x (wim a (wn b))
    (implicationVacuity x a (wn b) ha (negationVacuity x b hb))

def Context.existsElim {Γ : List Nat} (x : Nat) {a b : Nat}
    (hv : Derivation (wim b (wal x b)))
    (p : Context Γ (wal x (wim a b))) (q : Context Γ (wex x a)) : Context Γ b := by
  let hn : Context (wn b :: Γ) (wn b) := .assumption (by simp)
  let hnb : Context (wn b :: Γ) (wal x (wn b)) :=
    .mp hn (.closed (negationVacuity x b hv))
  let hc : Context (wn b :: Γ) (wal x (wim (wn b) (wn a))) :=
    (p.up (wn b)).forallMP x (.closed (.all x (contraposition a b)))
  let ha : Context (wn b :: Γ) (wal x (wn a)) := hnb.forallMP x hc
  exact (Context.mp ha (q.up (wn b))).deduction.dne

def existentialMonotonicity (x : Nat) {a b : Nat} (p : Derivation (wim a b)) :
    Derivation (wim (wex x a) (wex x b)) :=
  contrapose (.mp (.all x (contrapose p)) (r2 x (wn b) (wn a)))

def liftImp (x : Nat) {a b : Nat} (p : Derivation (wim a b)) :
    Derivation (wim (wal x a) (wal x b)) := .mp (.all x p) (r2 x a b)

def Context.arrowCompose {Γ : List Nat} {a b c : Nat}
    (p : Context Γ (wim a b)) (q : Context Γ (wim b c)) : Context Γ (wim a c) :=
  .mp q (.mp p (.closed (Dominated.composition a b c)))

#print axioms membershipVacuity
#print axioms pointedSeparation
#print axioms Context.existsElim
end PA194Logic
