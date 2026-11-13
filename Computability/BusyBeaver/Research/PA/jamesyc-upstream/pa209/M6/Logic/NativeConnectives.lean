module
public import M6.Logic.NativeDeduction
@[expose] public section

/-! Finite numeric proof operations from pinned NumericHilbert238.v.
No semantic completeness: every output is an actual dominated proof tree. -/
namespace M6.PA.NativeCalculus

def Context.up {Γ : List Nat} {a : Nat} (p : Context Γ a) (h : Nat) :
    Context (h :: Γ) a := p.cut (fun _ hb => .assumption (List.mem_cons_of_mem h hb))

def Context.dne {Γ : List Nat} {a : Nat} (p : Context Γ (wn (wn a))) : Context Γ a :=
  .mp p (.closed (doubleNegationElimination a))

def Context.andIntro {Γ : List Nat} {a b : Nat} (p : Context Γ a) (q : Context Γ b) :
    Context Γ (wa a b) :=
  (Context.mp (q.up (wim a (wn b)))
    (.mp (p.up (wim a (wn b))) (.assumption (by simp [wn])))).deduction

def Context.andLeft {Γ : List Nat} {a b : Nat} (p : Context Γ (wa a b)) : Context Γ a := by
  let ha : Context (a :: wn a :: Γ) a := .assumption (by simp)
  let hn : Context (a :: wn a :: Γ) (wn a) := .assumption (by simp)
  let arrow : Context (wn a :: Γ) (wim a (wn b)) :=
    ((Context.mp ha hn).explosion (wn b)).deduction
  exact (Context.mp arrow (p.up (wn a))).deduction.dne

def Context.andRight {Γ : List Nat} {a b : Nat} (p : Context Γ (wa a b)) : Context Γ b := by
  let hn : Context (wn b :: Γ) (wn b) := .assumption (by simp)
  exact (Context.mp (hn.lift a) (p.up (wn b))).deduction.dne

def contraposition (a b : Nat) : Derivation (wim (wim a b) (wim (wn b) (wn a))) := by
  let pa : Context [a, wn b, wim a b] a := .assumption (by simp)
  let pab : Context [a, wn b, wim a b] (wim a b) := .assumption (by simp)
  let pnb : Context [a, wn b, wim a b] (wn b) := .assumption (by simp)
  exact (Context.mp (.mp pa pab) pnb).deduction.deduction.deduction.empty

def contrapose {a b : Nat} (p : Derivation (wim a b)) : Derivation (wim (wn b) (wn a)) :=
  .mp p (contraposition a b)

def implicationCompose {a b c : Nat} (p : Derivation (wim a b))
    (q : Derivation (wim b c)) : Derivation (wim a c) :=
  .mp q (.mp p (Dominated.composition a b c))

def Context.forallMP {Γ : List Nat} (x : Nat) {a b : Nat}
    (p : Context Γ (wal x a)) (q : Context Γ (wal x (wim a b))) : Context Γ (wal x b) :=
  .mp p (.mp q (.closed (.r2 x a b)))

/-- GEN under hypotheses requires actual finite vacuity proofs for every
assumption; a free-variable semantic predicate is not substituted for them. -/
def Context.generalize {Γ : List Nat} {a : Nat} (p : Context Γ a) (x : Nat)
    (vacuity : ∀ h, h ∈ Γ → Derivation (wim h (wal x h))) : Context Γ (wal x a) :=
  match p with
  | .assumption h => .mp (.assumption h) (.closed (vacuity _ h))
  | .closed d => .closed (.all x d)
  | .mp p q => (p.generalize x vacuity).forallMP x (q.generalize x vacuity)

def equalityVacuity (a b x : Nat) (hxa : x ≠ a) (hxb : x ≠ b) :
    Derivation (wim (weq a b) (wal x (weq a b))) :=
  ((Context.closed (.guardedBundle a b x hxa hxb) : Context [] (bundle a b x)).andRight.andLeft).empty

def membershipVacuity (a b x : Nat) (hxa : x ≠ a) (hxb : x ≠ b) :
    Derivation (wim (wel a b) (wal x (wel a b))) :=
  ((Context.closed (.guardedBundle a b x hxa hxb) : Context [] (bundle a b x)).andRight.andRight).empty

#print axioms Context.andLeft
#print axioms Context.generalize
#print axioms equalityVacuity
#print axioms membershipVacuity
end M6.PA.NativeCalculus

