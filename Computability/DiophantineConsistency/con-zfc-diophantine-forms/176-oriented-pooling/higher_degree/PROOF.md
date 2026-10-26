# Exact monic projection of the pooled consistency equations

This component applies the acyclic unit-coefficient elimination method of
ProveIt report 152 to the new pooled equations. It claims a new application
and measured literal polynomials, not a new general elimination theorem.

## Integer zero-set bijection

Let a source equation be the sum of squares of finitely many integer
polynomial residuals. Select distinct rows and distinct variables so that
each selected row has the literal form

    epsilon_v * x_v + R_v = 0,    epsilon_v in {-1,1},

where x_v does not occur in R_v. Direct every selected variable v toward
the selected variables occurring in R_v. Require this finite dependency
graph to be acyclic. No condition is imposed on the signs of the variables.

Recursively define x_v = -epsilon_v * R_v in a topological order, using
the unselected variables as independent coordinates. Every restored value
is an integer polynomial in those independent coordinates. Delete the
selected rows, substitute these definitions into every retained residual,
and take the sum of their squares.

Any source integer zero satisfies the defining rows, so the recursive
values agree with its removed coordinates. Projection is therefore a zero
of the reduced equation. Conversely, at a reduced integer zero every
retained residual is zero, since a sum of integer squares is zero only
when every square is zero. Restoring the selected variables recursively
makes each deleted row zero by construction and every remaining source
row zero by substitution. Projection and restoration are inverse on the
integer zero sets.

The argument is finite algebra and integer order reasoning, formalizable
in PA and in ZFC. It uses no division, positivity witness, choice of a
root, or consistency assumption. Consequently it preserves the source's
proved equivalence between absence of integer zeros and Con(ZFC).

The source equations' arithmetic calibration is a separate dependency.
In particular, the new joint orientation/power certificate used by the
90-variable profile is justified by the surrounding report, not by the
finite projection checker.

## Complete finite polynomial definitions

Every delivered equation file contains a topologically ordered list of
nodes. The permitted nodes are an integer literal, an independent
variable, addition, subtraction, and multiplication. The field `output`
identifies the single final polynomial. The fields `residual_roots` list
the polynomials whose squares are summed. There is no variable exponent,
power oracle, unspecified numeral, or hidden quantified gate variable.
The nodes are a finite expression with sharing, so this specifies an
ordinary integer polynomial as exactly as its full expansion does.

The coefficient height of the expanded polynomial is not the maximum
literal constant. The latter is 384 in these circuits; the provided
coefficient-height bounds are intentionally loose. No expanded-support
count or exact expanded-coefficient height is claimed for these profiles.

## Exact degree certificate

For each circuit node, propagate a total-degree upper bound: literals
have degree zero, inputs degree one, multiplication adds degrees, and
addition/subtraction takes their maximum. At the same time substitute
each input by its stored integer direction times a formal parameter T,
and compute the coefficient at the propagated upper degree modulo the
stored integer modulus. At an addition, include only terms at the
maximum degree; at a product, multiply the leading coefficients.

A stored residual has nonzero coefficient at the maximum residual degree.
Nonzero modulo an integer greater than one proves that its corresponding
integer coefficient is nonzero; primality is unnecessary. Thus that
residual attains the upper bound. The top coefficient of the sum of its
and the other maximal-degree residuals' squares, evaluated in the same
integer direction, is a sum of integer squares containing a nonzero
square. It is strictly positive. The final polynomial therefore has
exactly twice the maximal residual degree.

This is a deterministic algebraic certificate. It does not infer
identity or degree from agreement at randomly sampled points.

## Genuine occurrence of every independent coordinate

Each circuit includes an integer point and the value of every first
partial derivative at that point modulo the stored modulus. The checker
recomputes those derivatives by exact reverse differentiation through the
circuit. Every value is nonzero. Hence every partial derivative is a
nonzero integer polynomial and every declared independent variable really
occurs in the final collected polynomial. This is stronger than merely
counting syntactic appearances in the circuit.

## Independent checker and limits

`verify.py` imports neither the search program nor the producer. It:

1. expands the retained quadratic source rows and checks them against the
   pinned literal P216 rows, thereby authenticating every possible pivot;
2. checks the unit coefficients, absence of the pivot variable from its
   remainder, uniqueness of pivots, and acyclic definitions;
3. reconstructs the structural expression of every imported source node
   under substitution, every residual, and the sum of squares;
4. checks exact degree, genuine variable occurrence, operation counts,
   and explicit coefficient-norm bounds;
5. rejects five deliberately corrupted copies of every circuit.

The builder separately reconstructs every selected equation byte for byte
from frozen pivot certificates. The checker's finite verifications do not
establish Con(ZFC), find a zero, or replace the source's unbounded
arithmetic proof. The heuristic search does not certify optimal arity or
minimal degree among all possible eliminations.

## Prior method

ProveIt report 152, `152-lucas-corrections/higher_degree/`, already gives
the acyclic monic method and profiles including 153 variables at degree 8,
125 at degree 16, 117 at degree 32, 111 at degree 64, 102 at degree 256, and 94 at
degree 65540. The present input equations and pivot choices differ. These
are comparisons within the direct proof-calculus branch, not a claim to
beat the repository's universal-polynomial constructions in variable
count.

Pinned reference:

https://github.com/VladimirReshetnikov/ProveIt/tree/315154b670d7bdb1679554734e417410c9b8187b/Computability/DiophantineConsistency/con-zfc-diophantine-forms/152-lucas-corrections/higher_degree
