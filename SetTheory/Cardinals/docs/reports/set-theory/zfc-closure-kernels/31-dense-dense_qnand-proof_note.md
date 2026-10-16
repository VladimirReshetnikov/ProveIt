# A bijective codec for fixed positive QNAND scope

This artifact implements the fixed-scope codec proposed during the present
report. Quantified NAND is prior work in the newly arrived ProveIt archive
`zfc_qnand_research.zip`, introduced at commit
`47e8871089dd8d5b5a912350f3285734041528bb`. Its syntax is an atom R(i,j), or
Q(A,B), where Q binds de Bruijn index zero in **both** children and denotes
`forall x, not (A and B)`. The scope-specific numerical presentation below
is a representation change; no binary machine or state improvement is claimed.

## Definition

For each positive natural d, let F_d be the finite formulas whose free
de Bruijn indices are below d. Thus R(i,j) belongs to F_d when i,j<d, and
Q(A,B) belongs to F_d when A and B belong to F_(d+1).

Use Cantor's pairing function P(a,b)=(a+b)(a+b+1)/2+b. Define

* E_d(R(i,j)) = i + d*j;
* E_d(Q(A,B)) = d² + P(E_(d+1)(A), E_(d+1)(B)).

The decoder D_d sends n<d² to R(n mod d, floor(n/d)). Otherwise it unpairs
n-d² as (a,b) and returns Q(D_(d+1)(a),D_(d+1)(b)). The hypothesis d>=1
is part of this presentation; zero scope is not passed to the implementation.

## Totality and two exact inverses

Cantor unpairing is a bijection and each unpaired component is at most its
input. If n>=d², both child codes therefore satisfy

`a,b <= n-d² < n`,

where strictness uses d>=1. Strong induction on n, simultaneously for all
positive d, proves total decoding and D_d(n) in F_d. The induction must be
uniform in d, because each recursive call increases the scope. A decoder
memo table must likewise use the pair (d,n), not n alone.

For n<d², Euclidean division reconstructs n from its quotient and remainder,
and both decoded atom indices are below d. For n>=d², the induction
hypotheses reconstruct both child codes and Cantor pairing reconstructs
n-d². Hence E_d(D_d(n))=n for every natural n.

Conversely, structural induction on a formula in F_d proves
D_d(E_d(A))=A. Atom codes lie below d²; compound codes lie at or above it.
The compound case uses the two induction hypotheses at scope d+1 and
injectivity of Cantor pairing. Therefore E_d and D_d are inverse bijections
between F_d and the natural numbers. In particular every code denotes one
legal formula, and there are no normalization aliases or unused codes.

## Semantics

For a nonempty domain U, binary relation R and environment e of exactly d
elements, evaluate an atom by R(e[i],e[j]). Evaluate Q(A,B) by requiring,
for every u in U, that A and B are not both true in the environment (u,e).
Both children receive precisely the same extended environment. Formula
induction gives semantic preservation of either codec roundtrip.

This does not constrain assignments to be injective. Distinct environment
slots may have identical values, and quantifiers range over the whole common
domain. Fixed syntactic scope therefore supplies none of the unwanted
separate-sort restrictions that defeated the earlier reduced calculus.

## Relationship to the prior raw codec

The prior QNAND codec is raw E(R(i,j))=2P(i,j) and
E(Q(A,B))=1+2P(E(A),E(B)). It gives every natural a formula, but does not
bound its free-variable scope. Its original EPSC wrapper compensates by
using `max(2,need[matrix])` slots and closing every actual parameter. The
present codec supplies a fixed-scope alternative, useful at d=4 for EPSC2.

Neither code is uniformly shorter in binary. At scope4, R(3,3) has dense
code15 and raw code48, whereas Q(R(0,0),R(0,0)) has dense code16 and raw
code1. The supplied deterministic syntax-generated corpus records both
directions; its average is a property of that corpus, not a universal law.
The bit convention assigns one bit to numeric zero and does not charge
framing, lengths, delimiters, interpreter code or initialization.

## Implementation and verification limits

`dense_qnand_codec.py` includes an iterative decoder whose memo keys contain
scope and code, a validating encoder, the prior raw encoder for comparisons,
ordinary finite-model formula semantics and a direct code evaluator.
`check_dense_qnand.py` tests both roundtrip directions, dynamic scope,
nested binders and 120,000 formula/structure/assignment cases. All sixteen
binary relations on a two-element domain occur, and assignments include
collisions. Host recursion, memory or arithmetic resource failures are not
caught as a refutation or an ordinary rejected natural-code candidate.

The mathematical proof is the induction above. Finite tests check the
implementation only. No proof-assistant formalization, refutation checker,
compiled state count, runtime bound or consistency result is inferred.
The actual compiler cost includes maintaining scope, computing d²,
threshold comparison, quotient/remainder by d and Cantor unpairing.

Reproduce with `python3 check_dense_qnand.py --output dense_qnand_results.json`
from this directory, with assertions enabled.
