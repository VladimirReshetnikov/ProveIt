import PA194FoundationOrdinalSuccessorClosureExtrema
namespace M6.PA.RelationalSource.Ordinal
open LO LO.FirstOrder ND

def intersectionFromAxiom {Γ : List Form} (a s : Term 0)
    (d : ND.Proof Γ intersectionFormula) : ND.Proof Γ (intersectionExists a s) := by
  cases a with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar i =>
    cases s with
    | bvar j => nomatch j
    | func f _ => nomatch f
    | fvar j =>
      have h := allElim _ (.fvar j) (allElim _ (.fvar i) d)
      convert h using 1 ; intersectionSyntax



def intersectionAxiomShift {Γ : List Form} (d : ND.Proof Γ intersectionFormula) :
    ND.Proof (shifted Γ) intersectionFormula := by
  convert shiftProof d using 1
  simp only [intersectionFormula]
  intersectionSyntax

def intersectionExtrema {Γ : List Form} (e : EqualityProofs Γ) (a b s : Nat)
    (ha : ND.Proof Γ (internalExtrema (.fvar a)))
    (hs : ND.Proof Γ (successor (.fvar a) (.fvar b)))
    (hsub : ND.Proof Γ (subset (.fvar s) (.fvar b)))
    (hne : ND.Proof Γ (nonempty (.fvar s)))
    (hi : ND.Proof Γ (intersectionExists (.fvar a) (.fvar s))) :
    ND.Proof Γ (extrema (.fvar s)) := by
  apply exsElim hi
  let σ : Formula 1 := intersection (Rew.bShift (.fvar a)) (Rew.bShift (.fvar s)) (.bvar 0)
  let C := σ.free :: shifted Γ
  have ht : ND.Proof C (intersection (.fvar (a+1)) (.fvar (s+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ] ; intersectionSyntax
  have dn : ND.Proof C (nonempty (.fvar (s+1))) := by
    convert up (shiftProof hne) σ.free using 1 ; ordinalSyntax
  have h := traceExtrema (e.shift.up σ.free) (a+1) (b+1) (s+1) 0
    (up (internalExtremaShift a ha) σ.free) (up (successorShift a b hs) σ.free)
    (up (subsetShift s b hsub) σ.free) ht dn
  convert h using 1 ; extremaSyntax

def successorInternalExtrema {Γ : List Form} (e : EqualityProofs Γ) (a b : Nat)
    (hi : ND.Proof Γ intersectionFormula)
    (ha : ND.Proof Γ (internalExtrema (.fvar a)))
    (hs : ND.Proof Γ (successor (.fvar a) (.fvar b))) :
    ND.Proof Γ (internalExtrema (.fvar b)) := by
  apply allIntro
  let p : Form := subset (.fvar 0) (.fvar (b+1)) ⋏ nonempty (.fvar 0)
  have hp : ND.Proof (p :: shifted Γ) p := assumption (by simp)
  have h := impIntro (intersectionExtrema (e.shift.up p) (a+1) (b+1) 0
    (up (internalExtremaShift a ha) p) (up (successorShift a b hs) p)
    (andLeft hp) (andRight hp)
    (intersectionFromAxiom (.fvar (a+1)) (.fvar 0) (up (intersectionAxiomShift hi) p)))
  convert h using 1 ; dsimp [p] ; extremaSyntax

/-- Actual finite Foundation derivation of closure. The equality-base
premises and the one fixed intersection axiom are exposed explicitly. -/
def successorDomain {Γ : List Form} (e : EqualityProofs Γ)
    (et : ND.Proof Γ transitivityFormula) (hi : ND.Proof Γ intersectionFormula)
    (a b : Term 0) (ha : ND.Proof Γ (domain a)) (hs : ND.Proof Γ (successor a b)) :
    ND.Proof Γ (domain b) := by
  cases a with
  | bvar i => nomatch i
  | func f _ => nomatch f
  | fvar i =>
    cases b with
    | bvar j => nomatch j
    | func f _ => nomatch f
    | fvar j =>
      have hr := andLeft ha
      have ht := andLeft hr
      have hm := andLeft (andRight hr)
      have hl := andLeft (andRight (andRight hr))
      have hx := andRight (andRight (andRight hr))
      exact andIntro (andIntro (successorTransitive e i j ht hs)
        (andIntro (successorMemberTransitive e i j ht hm hs)
          (andIntro (successorMemberLinear e et i j hl hs)
            (successorInternalExtrema e i j hi hx hs))))
        (successorMemberIr e i j (andRight ha) hs)

#print axioms intersectionExtrema
#print axioms successorInternalExtrema
#print axioms successorDomain
end M6.PA.RelationalSource.Ordinal

