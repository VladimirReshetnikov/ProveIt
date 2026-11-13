module
public import M6.Logic.NativeSubstitution
@[expose] public section

/-! Syntactic vacuity through all named constructors. The output is a finite
native proof, not a semantic assertion about free variables. This is the
generalization prerequisite used by the actual alpha/readback compiler. -/
namespace M6.PA.NativeCalculus

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
    (.mp (.all x (Dominated.k b a)) (.r2 x b (wim a b)))
  let hn : Context [a, wn a] (wn a) := .assumption (by simp)
  let hp : Context [a, wn a] a := .assumption (by simp)
  let hnot : Derivation (wim (wn a) (wim a b)) :=
    ((Context.mp hp hn).explosion b).deduction.deduction.empty
  let haLift : Derivation (wim (wn a) c) := implicationCompose (negationVacuity x a ha)
    (.mp (.all x hnot) (.r2 x (wn a) (wim a b)))
  let pa : Context [a, wim a b] a := .assumption (by simp)
  let pab : Context [a, wim a b] (wim a b) := .assumption (by simp)
  let pc : Context [a, wim a b] c := .mp (.mp pa pab) (.closed hbLift)
  let pna : Context [wn a, wim a b] (wn a) := .assumption (by simp)
  let pnc : Context [wn a, wim a b] c := .mp pna (.closed haLift)
  exact (Context.casesOnFormula a pc pnc).deduction.empty

def universalVacuity (x y a : Nat) (h : Derivation (wim a (wal x a))) :
    Derivation (wim (wal y a) (wal x (wal y a))) :=
  implicationCompose (.mp (.all y h) (.r2 y a (wal x a))) (.r4 y x a)

def Named.vacuity (p : Named) (v : Nat)
    (hf : p.free v = false) (hb : p.binders v = false) :
    Derivation (wim p.encode (wal v p.encode)) :=
  match p with
  | .truth => .mp (.all v .truth) (Dominated.k (wal v 0) 0)
  | .neg p => negationVacuity v p.encode (p.vacuity v hf hb)
  | .imp p q => by
    simp only [free,binders,Bool.or_eq_false_iff] at hf hb
    exact implicationVacuity v p.encode q.encode (p.vacuity v hf.1 hb.1) (q.vacuity v hf.2 hb.2)
  | .mem a b => by
    simp only [free,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hf
    exact membershipVacuity a b v hf.1 hf.2
  | .eq a b => by
    simp only [free,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hf
    exact equalityVacuity a b v hf.1 hf.2
  | .all a p => by
    simp only [binders,Bool.or_eq_false_iff,beq_eq_false_iff_ne] at hb
    have hfp : p.free v = false := by simpa [free,hb.1] using hf
    exact universalVacuity v a p.encode (p.vacuity v hfp hb.2)

def Named.outputVacuity (p : Named) : Derivation (wim p.encode (wal p.encode p.encode)) :=
  p.vacuity p.encode p.encoded_output_free_fresh p.encoded_output_binders_fresh

#print axioms Named.vacuity
#print axioms Named.outputVacuity
end M6.PA.NativeCalculus

