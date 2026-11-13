# Strict three-field certificates: proof and scope

## Frozen candidates

`checker_313_353.py`: 313 significant tokens, 353 Python AST nodes, 701 normalized
UTF-8 bytes. `split.py`: 306 tokens, 362 nodes, 668 normalized bytes. These are
measurements under the installed Python runtime using the repository's
`ast.unparse(ast.parse(source)) + '\n'` convention. Neither program is a byte
record. They implement the same proof protocol; their differences are ordinary
Python control-flow and import/reader layout.

The reference is `readable_three_field_strict.py`. It is explanatory source;
the compact programs, not the readable reference, are the measured deliverables.
The native calculus, arithmetic language, induction principle and ordinary
interpretation are inherited unchanged from the pinned ConciseIPRA repository.
There is no new mathematical axiom deletion in this package.

## Input contract

Input is one complete JSON value. Its Python printed form must contain only
`0123456789-[], `; otherwise execution cannot reach `ACCEPT`. This admits exactly
finite trees of Python integers and lists among JSON values. In particular
Booleans, floats, nulls, strings and objects are excluded, including in unused
parts of the input. The program then requires a stack supporting `pop`, whose
last item is the proposed closed goal. Each consumed instruction has exactly
three fields `(s,u,t)`.

The first no-image traversal validates the closed public Eq/D grammar with the
uniform-zero encoding `P^ed_1`: list arity at depth d must be 1 or `2+d mod 2`,
and a retained scalar must be odd, at odd depth, and satisfy `0 <= a < d`.
Public zero is the scalar 1. The depth increment at an r-child list is `5-r`.
This is exactly the validation phase of the inherited strict checker. Successful
initial traversal preserves the input goal. No public-language assumption is
left to the caller.

After initial validation, each context contains the neutral integer 0. This
ends the validation phase; intermediate raw syntax has the inherited auxiliary
reading. All no-image entry scans and all scope bounds are retained.

## Protocol

At a call with context g, goal A and local scope floor k:

1. Apply the no-image opening to A. Return if it belongs to g.
2. Add the neutral resource 0 and read `(s,u,t)`.
3. If `O_k(t;u,0) = A` literally, replace A by `O_k(t;s,0)`, replace s by
   `[s,u]` when s is truthy and `[t,t,t]` otherwise, and set u to 0.
4. If u is truthy, form the usual zero/successor computation hypothesis.
   Otherwise recursively prove s from g, then use `s*3` if s is truthy, or
   open the matrix of A at witness t if s is false-valued.
5. Decrease the local floor to `k-1`. Open the new hypothesis at that fresh
   parameter when s is truthy or `len(A)%2 == u`; otherwise open it at zero.
   Recur on the opened goal with the hypothesis added.

The empty list and the integer 0 remain distinct false-valued fields: u=[]
selects native introduction by cases, while u=0 selects progress at a literal
equation. This distinction must not be replaced by truthiness alone.

## Soundness: what actually changes

Use the auxiliary reading, semantic-opening and freshness lemmas of the pinned
article (chapter 11). Induct on a finite successful tree of calls, maintaining
that the goal and each inherited context member are closed at entry floor k.

* Entry membership is the hypothesis rule. The initial validation guarantees
  that the final conclusion is an actual closed public formula.
* In the endpoint-match case, the reconstructed major `[s,u]` or `[t,t,t]` is
  recursively proved before its triple is added. The semantic opening lemma
  makes this equality transport or closure specialization. The new minor goal
  is closed at the old floor. Inferred majors are never accepted unchecked.
* With u false and s truthy, the triple of s opens an existential closure at a
  fresh parameter when s is unary. All other arities have the inherited neutral
  reading. This is the established paired-binder elimination argument.
* With u and s false, the matrix is opened at the witness before decreasing
  the floor. Thus the witness cannot name the new eigenparameter. The test
  `len(A)%2 == u` allows progress for equations only and preserves the special
  u=[] case mode. Compound matrices receive the zero image. Unexpected raw
  arities are handled by the inherited neutral-reading cases.
* With u truthy, the generated hypothesis is the established computation
  frame. A nonzero predecessor s now selects a fresh image, rather than the
  zero image of the four-field strict reference. This is sound by the article's
  **zero-instance computation lemma**, `cert:lem:zeroinstance`: after substituting
  zero for all newly admitted names, the hypothesis is an instance of I0 or IS.
  The goal and old context are closed at the old floor and contain none of
  those names. Apply the continuation induction hypothesis in the ordinary
  realization T_eq and specialize the fresh names to zero, using the supply
  lemma `cert:lem:supply`. The resulting arithmetic hypothesis is an axiom and
  can be cut away.

Do not strengthen the last point to “the generated H(z) is always itself a
computation axiom.” Raw dummy-slot aliases can make that false; it is H(0)
that the inherited lemma guarantees. Do not use substitution admissibility in
a source-restricted presentation when the ordinary realization is what supplies
that substitution.

The endpoint match here is tested at the old floor. In the strict reference's
compressed final expression it may be tested after the decrement. Consequently
we do **not** claim identity of accepted raw certificate stacks or an exact
step-for-step compiler on every malformed auxiliary tree. The direct soundness
argument above uses the earlier-test base protocol, where the relevant scope
lemmas apply without this ambiguity.

## Completeness and canonical certificate compilation

Start with the repository's canonical certificates for the native Eq/D public
theorems, with public zero recoded by 1. Use these three-field records:

| Native action | New record |
|---|---|
| Transport from s=u through template F | `[s,u,F]` |
| Closure specialization to u, with matrix B | `[0,u,B]` |
| Eliminate a paired formula M | `[M,0,0]` |
| Zero or successor computation with predecessor s, seed u, body t | `[s,u,t]` |
| Introduce by cases at witness w | `[0,[],w]` |
| Introduce by equation progress at witness w | `[0,0,w]` |

Append the recursively compiled major and continuation records in consumption
order; serialize the stack in reverse order followed by the goal. Numeric
source zero is encoded 1, so it remains truthy in transport. Control source 0
selects closure specialization or introduction.

At a genuine transport/specialization, the endpoint match holds, so the inferred
major is exactly the one whose proof is supplied. At computation and introduction
records, a canonical term cannot accidentally equal a canonical formula: term
trees have no binary node, whereas every formula tree ends in a binary equation.
The computation hypothesis is already closed at the old floor, so choosing a
fresh or zero image makes no difference. Other branches preserve the native
inferences, including the []/0 distinction. Thus every closed public theorem
has an accepted new certificate.

Soundness and completeness identify the **accepted public theorem language**
with that of the inherited strict native checker. The ordinary realization and
both formula translations are unchanged. Composing with the repository's
established whole-domain identity bi-interpretation gives equiconsistency and
bi-interpretability with iPRA. This transfers the inherited result; it is not an
independent formalization of the arithmetic bridge.

## Implementation equivalences

Moving the hypothesis expression into h, then performing `k -= 1`, preserves
its evaluation at the old floor and all subsequent openings at the new floor.
The image test depends on s, u and A, not on k. The procedures have no returned
proof object; every successful call returns None, and that false value is used
only in the same Boolean chain as in the reference.

Replacing the missing-image default c by 0j saves one AST node. Both are rejected
when traversed: the function fails integer/list arithmetic, while 0j reaches an
invalid ordered comparison. If a substitution image is not needed, neither
sentinel is inspected. No successful traversal returns either sentinel.

The inline opener, negated branch instead of early return, imported reader name,
and reader assignment expressions change neither the order nor the values of
successful evaluations. They only trade tokens, nodes and bytes.

## Verification and limits

All 16 inherited accepted supply fixtures compile to the three-field protocol
and are accepted by both frozen programs and the readable reference; they include
induction with a used hypothesis, native atomic case introduction, computations,
transport, closure elimination, and derived zero-source transport. Further
rejections cover false equations, malformed public grammar/types, missing or
wrong-arity records, and perturbations of compiled goals. The supplied verifier
also runs the checkers with and without Python -O.

The mathematical soundness and completeness arguments, not finite tests,
justify the theorem-language equivalence. Resource exhaustion is rejection in
these concrete programs; as in the repository's metric, completeness refers to
finite successful runs without a fixed global memory or recursion bound.
