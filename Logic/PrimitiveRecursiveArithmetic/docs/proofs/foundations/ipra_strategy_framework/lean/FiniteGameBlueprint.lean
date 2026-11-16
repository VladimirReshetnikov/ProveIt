/-!
Finite strategy framework: Lean 4 standalone *blueprint*.
No `sorry`, axioms, or kernel-checked iPRA claims are hidden here.
The definitions are executable Lean metatheory, not PR symbols in ProveIt.
To complete the work, encode these algorithms using ConciseIPRA.PR
composition/recursion and construct Prf PRAAx derivations.
-/
namespace FiniteGame

-- Loop definitions use structurally recursive Nat recursion.
def allB : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => allB n p && p n

def anyB : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n + 1, p => anyB n p || p n

-- Sentinel: if there is no success below b, return b.
def firstB : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, p =>
      let k := firstB n p
      if k < n then k else if p n then n else n + 1

-- An externally supplied bounded atomic relation and bound.
structure BoundedAtom where
  bound : Nat → Nat
  holds : Nat → Nat → Bool

def someB (a : BoundedAtom) (x : Nat) : Bool :=
  anyB (a.bound x) (a.holds x)

def everyB (a : BoundedAtom) (x : Nat) : Bool :=
  allB (a.bound x) (a.holds x)

-- Finite game tree. In a production embedding, tree syntax is indexed
-- by a fixed formula, so no universal evaluator for PR functions is needed.
inductive Tree where
  | leaf : Bool → Tree
  | existsN : List Tree → Tree
  | forallN : List Tree → Tree
  deriving Repr

-- A finite certificate represents a selected branch or all branches.
inductive Cert where
  | leaf : Bool → Cert
  | picked : Bool → Nat → Cert → Cert
  | spread : Bool → List Cert → Cert
  deriving Repr

-- TARGET LEMMAS (not asserted as theorem declarations):
-- 1. firstB b p < b ↔ ∃ i, i < b ∧ p i = true
-- 2. firstB b p < b → p (firstB b p) = true
-- 3. firstB b p < b → ∀ i < firstB b p, p i = false
-- 4. allB b p = true ↔ ∀ i < b, p i = true
-- 5. anyB b p = true ↔ ∃ i < b, p i = true
-- 6. checker_sound / checker_complete for fixed-depth games
-- 7. object-level reflection to Prf PRAAx through primitive recursion.
--
-- The proofs of (1)-(5) use induction on b and Bool cases. For (6)
-- use induction on Tree and simultaneous List induction; at player nodes
-- use the least child of the desired winner. For (7) replace all higher-
-- order parameters by PR codes for the particular fixed formula.
end FiniteGame
