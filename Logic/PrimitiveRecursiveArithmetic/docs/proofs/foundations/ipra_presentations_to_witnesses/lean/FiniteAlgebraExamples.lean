import FiniteAlgebraTargets

/-!
The paper's finite elliptic section, evaluated by the complete target programs.
These `#eval` lines are executable diagnostics, not object-iPRA derivations.
The returned values are recorded in the build log.
-/

namespace FiniteAlgebra.Examples

open Targets

def term (c : Rat) (a b : Nat) : Polynomial 2 :=
  [{ coefficient := c, exponents := #v[a, b] }]

def one : Polynomial 2 := term 1 0 0
def x : Polynomial 2 := term 1 1 0
def y : Polynomial 2 := term 1 0 1
def xy : Polynomial 2 := term 1 1 1

def equations : Vector (Polynomial 2) 2 := #v[
  term 4 0 2 ++ term (-4) 3 0 ++ x ++ term (-4) 0 0,
  term 2 2 0 ++ term (-1) 1 0]

def certificate : Certificate 2 2 4 where
  basis := #v[one, x, y, xy]
  unitCoefficients := #v[1, 0, 0, 0]
  unitWitness := #v[[], []]
  delta := #v[2, 1]
  action := #v[
    #v[#v[0, 2, 0, 0], #v[0, 1, 0, 0], #v[0, 0, 0, 2], #v[0, 0, 0, 1]],
    #v[#v[0, 0, 1, 0], #v[0, 0, 0, 1], #v[1, 0, 0, 0], #v[0, 1, 0, 0]]]
  actionWitness := #v[
    #v[#v[[], []], #v[[], one], #v[[], []], #v[[], y]],
    #v[#v[[], []], #v[[], []],
      #v[term (1/4) 0 0, term (1/2) 1 0 ++ term (1/4) 0 0],
      #v[term (1/4) 1 0, term (1/2) 2 0 ++ term (1/4) 1 0]]]

#eval certificateOK equations certificate
#eval (List.finRange 2).map (fun k => columnBound certificate.action[k])
#eval (grid certificate).length
#eval enumerate equations certificate

end FiniteAlgebra.Examples

