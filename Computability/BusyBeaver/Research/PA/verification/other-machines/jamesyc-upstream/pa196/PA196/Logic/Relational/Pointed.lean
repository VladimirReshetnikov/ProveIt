module
public import PA196.Logic.Relational.Freshening
@[expose] public section

namespace PA196.Logic.Relational
open M6.Source

def pointedExistential (a b c : Nat) (ha : c ≠ a) (hb : c ≠ b) :
    Proof (wex c (wa (PA196.Logic.separation a b c) (PA196.Logic.point a b c))) := by
  let s := PA196.Logic.separation a b c
  let p := PA196.Logic.point a b c
  let hn : Proof (wn (wal c (wim s (wn p)))) := pointedSeparation a b c ha hb
  let hall : Proof (wim (wal c (wn (wn (wim s (wn p))))) (wal c (wim s (wn p)))) :=
    .mp (.all c (doubleNegationElimination (wim s (wn p)))) (r2 c _ _)
  exact .mp hn (contrapose hall)

def namedAnd (p q : Named) := M6.PA.NativeCalculus.Named.neg (.imp p (.neg q))
def namedExists (x : Nat) (p : Named) := M6.PA.NativeCalculus.Named.neg (.all x (.neg p))

def rawPointedAt (a b c : Nat) (p : Named) : Named :=
  namedExists c (namedAnd
    (.all b (namedAnd (.imp (.mem a b) (.imp p (.mem c b))) (.imp (.mem c b) p)))
    (.imp p (.mem c b)))

def rawPointedNamed (a b z : Nat) (p : Named) : Named :=
  rawPointedAt a b (relationalCode z p) p

theorem rawPointedCode (a b z : Nat) (p : Named) :
    relationalCode z (rawPointedNamed a b z p) =
      wex (relationalCode z p) (wa
        (PA196.Logic.separation a b (relationalCode z p))
        (PA196.Logic.point a b (relationalCode z p))) := by
  simp only [rawPointedNamed,rawPointedAt,namedExists,namedAnd,relationalCode,
    PA196.Logic.separation,PA196.Logic.point,wex,wa,wn,wim,wal,wel]

def rawPointedProof (a b z : Nat) (p : Named)
    (ha : relationalCode z p ≠ a) (hb : relationalCode z p ≠ b) :
    Proof (relationalCode z (rawPointedNamed a b z p)) :=
  (rawPointedCode a b z p).symm ▸ pointedExistential a b (relationalCode z p) ha hb

theorem rawPointedReserved (a b z : Nat) (p : Named)
    (hp : p.names z = false) (ha : z ≠ a) (hb : z ≠ b)
    (hc : z ≠ relationalCode z p) : (rawPointedNamed a b z p).names z = false := by
  simp [rawPointedNamed,rawPointedAt,namedExists,namedAnd,M6.PA.NativeCalculus.Named.names,hp,ha,hb,hc]

def paddingLabel (a b z : Nat) (p : Named) := a+b+z+p.encode+1
def paddedProperty (a b z : Nat) (p : Named) := M6.PA.NativeCalculus.Named.all (paddingLabel a b z p) p

theorem paddedCode_bounds (a b z : Nat) (p : Named) :
    a < relationalCode z (paddedProperty a b z p) ∧
    b < relationalCode z (paddedProperty a b z p) ∧
    z < relationalCode z (paddedProperty a b z p) := by
  have hp := PA196.Logic.pair_bounds (relationalCode z p) (paddingLabel a b z p)
  simp only [paddedProperty,relationalCode,wal,paddingLabel]
  dsimp [paddingLabel] at hp
  omega

theorem paddedReserved (a b z : Nat) (p : Named) (hp : p.names z = false) :
    (paddedProperty a b z p).names z = false := by
  have hz : z ≠ paddingLabel a b z p := by unfold paddingLabel; omega
  simp [paddedProperty,M6.PA.NativeCalculus.Named.names,hp,hz]

def paddedRawPointedProof (a b z : Nat) (p : Named) :
    Proof (relationalCode z (rawPointedNamed a b z (paddedProperty a b z p))) :=
  rawPointedProof a b z _ (Ne.symm (Nat.ne_of_lt (paddedCode_bounds a b z p).1))
    (Ne.symm (Nat.ne_of_lt (paddedCode_bounds a b z p).2.1))

def paddedFreshPointedProof (a b z : Nat) (p : Named)
    (hp : p.names z = false) (ha : z ≠ a) (hb : z ≠ b) :
    Proof (relationalCode z
      ((rawPointedNamed a b z (paddedProperty a b z p)).freshen
        ((rawPointedNamed a b z (paddedProperty a b z p)).encode+z+1))) := by
  have hr := rawPointedReserved a b z (paddedProperty a b z p)
    (paddedReserved a b z p hp) ha hb (Nat.ne_of_lt (paddedCode_bounds a b z p).2.2)
  exact .mp (paddedRawPointedProof a b z p)
    (relationalCanonicalFreshening _ z hr).1

def forallStrip (x a : Nat) (hv : Proof (wim a (wal x a))) : Proof (wim (wal x a) a) := by
  let h : Context [wal x a] (wal x a) := .assumption (by simp)
  let hi := h.forallMP x (.closed (.all x (Dominated.k a (weq 0 x))))
  exact (Context.existsElim x hv hi (.closed (r1 x 0))).deduction.empty

def paddedEquivalence (a b z : Nat) (p : Named) :
    Proof (wim (relationalCode z p) (relationalCode z (paddedProperty a b z p))) ×
    Proof (wim (relationalCode z (paddedProperty a b z p)) (relationalCode z p)) := by
  let q := paddingLabel a b z p
  have hqz : q ≠ z := by dsimp [q,paddingLabel]; omega
  have hnames : p.names q = false := by
    cases he : p.names q with
    | false => rfl
    | true => have hb := p.names_bound q he; dsimp [q,paddingLabel] at hb; omega
  let hv := relationalCodeVacuity p z q hqz
    (names_free_false p q hnames) (names_binders_false p q hnames)
  exact ⟨hv,forallStrip q _ hv⟩

abbrev Bi (a b : Nat) := Proof (wim a b) × Proof (wim b a)
def Bi.refl (a : Nat) : Bi a a := ⟨identity a,identity a⟩
def Bi.neg {a b : Nat} (p : Bi a b) : Bi (wn a) (wn b) := ⟨contrapose p.2,contrapose p.1⟩
def Bi.imp {a aa b bb : Nat} (p : Bi a aa) (q : Bi b bb) : Bi (wim a b) (wim aa bb) :=
  ⟨implicationCongruence p.2 q.1,implicationCongruence p.1 q.2⟩
def Bi.all {a b : Nat} (x : Nat) (p : Bi a b) : Bi (wal x a) (wal x b) :=
  ⟨forallCongruence x p.1,forallCongruence x p.2⟩
def Bi.and {a aa b bb : Nat} (p : Bi a aa) (q : Bi b bb) : Bi (wa a b) (wa aa bb) :=
  (p.imp q.neg).neg
def Bi.exs {a b : Nat} (x : Nat) (p : Bi a b) : Bi (wex x a) (wex x b) := (p.neg.all x).neg

def rawPointedCongruence (a b c z : Nat) (p q : Named)
    (h : Bi (relationalCode z p) (relationalCode z q)) :
    Bi (relationalCode z (rawPointedAt a b c p))
      (relationalCode z (rawPointedAt a b c q)) :=
  (((((Bi.refl (wel a b)).imp (h.imp (Bi.refl (wel c b)))).and
      ((Bi.refl (wel c b)).imp h)).all b).and (h.imp (Bi.refl (wel c b)))).exs c

/-- The padding is removed by an actual finite equivalence proof. The chosen
output label remains the explicit large padded-property code. -/
def pointedPropertyProof (a b z : Nat) (p : Named) :
    Proof (relationalCode z
      (rawPointedAt a b (relationalCode z (paddedProperty a b z p)) p)) :=
  .mp (paddedRawPointedProof a b z p)
    (rawPointedCongruence a b _ z p (paddedProperty a b z p) (paddedEquivalence a b z p)).2

#print axioms paddedRawPointedProof
#print axioms paddedFreshPointedProof
#print axioms pointedPropertyProof
end PA196.Logic.Relational

