import PA194SemanticCollisionScope

/-! The equality-neighborhood translation needs an observational extensionality
assumption. This uses explicit named formulas with PA194's quantifier encoding;
it does not assume the PA196 native total decoder is a PA194 decoder. -/
namespace PA194SemanticExtensionality
open M6.PA.NativeCalculus

def emptyRelation (_ _ : Bool) : Prop := False
def assignment (v : Nat) : Bool := if v = 0 then false else true

def namedAnd (p q : Named) : Named := .neg (.imp p (.neg q))
def namedIff (p q : Named) : Named := namedAnd (.imp p q) (.imp q p)
def namedNeighborhood (a b z : Nat) : Named :=
  namedAnd (.all z (namedIff (.mem a z) (.mem b z)))
    (.all z (namedIff (.mem z a) (.mem z b)))

def encode194 : Named → Nat
  | .truth => 0
  | .imp p q => PA194Logic.wim (encode194 p) (encode194 q)
  | .neg p => PA194Logic.wn (encode194 p)
  | .mem a b => PA194Logic.wel a b
  | .eq a b => PA194Logic.weq a b
  | .all a p => PA194Logic.wal a (encode194 p)

theorem emptyRelation_irreflexive : ∀ x, ¬ emptyRelation x x := by simp [emptyRelation]

theorem source_equality_false : ¬ (Named.eq 0 1).eval emptyRelation Eq assignment := by
  simp [Named.eval,assignment]

theorem named_neighborhood_true : (namedNeighborhood 0 1 2).eval emptyRelation Eq assignment := by
  simp [namedNeighborhood,namedAnd,namedIff,Named.eval,emptyRelation]

theorem target_encoding_agrees :
    encode194 (namedNeighborhood 0 1 2) =
      PA194Logic.Relational.relationalCode 2 (.eq 0 1) := by
  rfl

#print axioms emptyRelation_irreflexive
#print axioms source_equality_false
#print axioms named_neighborhood_true
#print axioms target_encoding_agrees
end PA194SemanticExtensionality
