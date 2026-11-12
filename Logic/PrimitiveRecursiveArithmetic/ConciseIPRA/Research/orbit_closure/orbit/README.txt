TARGET-FREE SCALAR ORBIT UNIQUENESS
=================================

This is a complete, strict, standalone implementation of the Orbit rule on
the raw native Eq/Q/D calculus. It is an equivalent presentation of scalar
UR, not a new smallest-checker claim. The exact comparison is:

Program                 Normalized bytes  Tokens  AST nodes
scalar_ur.py                         3393    1124       1175
orbit_templates.py                   3400    1132       1178
orbit_inferred.py                    3455    1145       1194

The selected orbit_inferred.py takes only a proposed closure and a premise
proof. It reads f and h from the closure; it takes no separate target or
numerical template fields. Checking those structural conditions costs more
than the original UR instruction. The explicit-template companion removes
only the target field and is seven bytes larger than its matched UR control.
None approaches the repository's compact coordinate minima.

FILES
-----
code/orbit_inferred.py    Complete selected standalone checker.
code/orbit_templates.py  Matched target-free explicit-template companion.
code/scalar_ur.py        Normalized exact upstream UR control.
translate_ur.py          Untrusted general finite-proof UR-to-Orbit translator.
validate.py              Untrusted fixtures and measurement driver.
validation/results.json  Actual bounded process-check results and metrics.
reference/               Exact fetched upstream files plus generated fixtures.

COMMON LANGUAGE AND RULES
-------------------------
The terms are ['v',i], ['z'], ['s',t], ['i',n,a,h]. Indices are de Bruijn:
index zero is the nearest binder. Only the iterator body h binds a state.
Formulas are ['=',s,t], ['q',B], ['d',B]. Q binds one variable. D binds two:
its closure variable has index 0 and its existential witness has index 1.
Ordinary readings are Q_y B = B(0) -> forall y B(y) and
D_x,y B = exists x (B(x,0) -> forall y B(x,y)).

Unchanged inference tags: hyp, zero, succ, tr (crossed one-term equality
transport), qe, de, di (case introduction). The UR control additionally has
['ur',f,h,t,p]. The new checkers replace that rule only.

Every certificate is a JSON object with exactly the keys:
  variables: a nonnegative exact integer;
  context: a list of formulas in that numerical scope;
  goal: a formula in that numerical scope;
  proof: the tagged proof tree.
Normal exit and exactly ACCEPT followed by a newline mean acceptance.
Unsuccessful inputs exit nonzero. Python assertions are not used.

INFERRED ORBIT INSTRUCTION
--------------------------
  ['orbit', ['q', ['=', f, ['i', ['v',0], a, H]]], p]

At ambient scope n, f and a have scope n+1. H has scope n+2:
its state is index 0, its outer counter is index 1, and passive parameters
have indices 2 and higher. The checker:

1. Validates the entire displayed closure in scope n.
2. Removes the outer counter coordinate from H, rejecting every occurrence
   of that coordinate, including occurrences under further iterator binders.
   The resulting h has scope n+1 and its only active slot is the state.
3. Requires a to be shift(f[0]), the zero instance of f shifted back under
   the closure binder. This is literal syntax on raw terms.
4. Checks p under the shifted original context and one fresh numerical
   parameter z. No induction hypothesis is added. Its conclusion must be
   f(Sz)=h(f(z)).
5. Returns the proposed closure exactly.

Counter independence is indispensable. For f(y)=y and H(y,u)=S(y), the
recurrence is reflexive but the purported orbit would assert
1=I(1,0;u.2)=2. The selected checker rejects this attack before checking p.

The coordinate-removal implementation uses the existing substitution routine:
  h = sub(['q', H], ['v', n])[1]
  term(h, n+1)
The artificial Q protects the state slot. An occurrence of the forbidden
counter becomes an out-of-scope sentinel; the subsequent term validation
rejects it. A legitimate passive variable drops one index. The same proof
applies beneath every additional binder because sub shifts its replacement.

EXPLICIT-TEMPLATE COMPANION
----------------------------
  ['orbit', f, h, p]
The scopes and premise are those of UR, with its target field deleted.
The checker constructs Q_y(f(y)=I(y,f(0);u.h)) itself.

MATHEMATICAL EQUIVALENCE
-------------------------
Orbit yields each UR instance by QE. The zero instance required by QE is
f(0)=I(0,f(0);u.h), the symmetric zero-computation equation. The included
translator implements this construction recursively for arbitrary finite
UR proof trees; every other inference tag is preserved.

Conversely, given the recurrence premise, UR gives the orbit equation at
S(z) in any fresh scope, even under the unused assumption that its zero
instance holds. DI by cases at an unused dummy witness followed by DE gives
the corresponding Q closure. This uses only ordinary admissible weakening
and fresh renaming, not an additional induction rule. Therefore both
calculi have precisely the same open consequences as scalar UR.

Together with the inherited scalar-UR equivalence, this transfers the
whole-domain, actual-equality bi-interpretation with full first-order iPRA.
The new code and translation have not been verified in a proof assistant.
The finite executable tests supplement the mathematical proof; they do not
prove universal soundness or completeness.

REPRODUCE
---------
  python3 reference/verify.py
  python3 validate.py
  python3 code/orbit_inferred.py < validation/closed_identity_orbit.json
  python3 translate_ur.py inferred < reference/examples/scalar_ur_ur_nested_iterator_scope.json

The recorded Orbit run contains 156 normal/optimized checker processes:
92 expected acceptances, 64 expected rejections, zero mismatches. Both
translator modes also passed an actual command-line translation followed by
an independently invoked target checker. The inherited UR/QI reference
suite contains a separate 66 process checks, all passing.

SOURCE
------
Repository: VladimirReshetnikov/ProveIt
Frozen commit: 62396b06020f794fa6dc01b4025a6a5db9d4d28a
Upstream path:
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/scalar_uniqueness/code/uniqueness

reference/scalar_ur.py, baseline_qi.py, README.md, measure.py, and verify.py
are exact fetched upstream text. The code/scalar_ur.py control is its
ast.unparse-normalized form. The common checker body is inherited from that
source. Only the orbit instruction is new. The repository's MIT No
Attribution license applies to inherited material.
