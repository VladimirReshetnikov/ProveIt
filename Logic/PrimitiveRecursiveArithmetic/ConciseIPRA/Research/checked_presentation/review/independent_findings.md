# Independent mathematical audit

Snapshot: ProveIt commit `6ffc49f55d355b548f7a8e1530570aee5de086b3`,
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`.

## The complexity target

The README specifies significant Python tokens, Python AST nodes and UTF-8
bytes after `ast.unparse` normalization. Its table records best implementations
of the collected presentations. These numbers constitute an observed lower
envelope of the comparison set, not a theorem that every iPRA presentation
requires at least those numbers. The request can sensibly mean strictly
improving that envelope; no absolute minimality result follows from an
improvement.

## A rigorous obstruction to an opaque universal-evaluator shortcut

Assume a numerical term language effectively represents every unary primitive
recursive function. Assume program-code formation and substitution of a
numeral are primitive recursive. There cannot be a primitive recursive
function U(e,n) that evaluates every valid unary term code e at n (with any
values whatsoever on invalid codes).

Proof: if U were primitive recursive, d(n)=U(n,n)+1 would be primitive
recursive. Choose a valid unary term code e_d representing d. Then
U(e_d,e_d)=d(e_d)=U(e_d,e_d)+1, a contradiction.

Consequently a normalizer for arbitrary closed primitive-recursive iterator
terms cannot be primitive recursive if its output is a numeral with primitive
recursive decoding. Fixed-term evaluation is primitive recursive; uniform
evaluation across all syntax is a different assertion. This does not invalidate
the repository's normal-form presentations, which can employ an externally
total recursive normalizer. It does invalidate an argument that deletes the
iterator/compiler and silently assumes a primitive recursive universal evaluator.
It is also necessary to distinguish the external proof checker's termination
from totality provable inside iPRA.

## Relevant primary source on deleting induction

Harvey Friedman, 'Provable equality in primitive recursive arithmetic with and
without induction', Pacific Journal of Mathematics 57(2) (1975), 379--392.
Publisher PDF:
https://msp.org/pjm/1975/57-2/pjm-v57-n2-p10-s.pdf

Theorem 8 (p.391) says that primitive recursion equations with definition by
cases and successor axioms are conservative over the corresponding subsystem
for a closed set of primitive-recursive symbols. The discussion immediately
before and after it states that this theory does not prove
G(x)=S(x) for G(0)=S(0), G(S(x))=S(G(x)), or commutativity of addition.

This offers a route toward the repository's open independence question for QI,
but is not yet a solution: the native binding iterator requires coherence under
substitution of parameters and bodies. A compilation into independently named
primitive-recursive symbols cannot simply assume the required identities in a
theory without induction. The finite-subsystem model starts easily with a
standard successor chain and a separate integer successor chain, interpreting
G with a different shift on the latter; extending it to all operations is what
the source theorem provides, not automatically to the native binding operation.

## Alternative domain considered

Finite binary trees support pairing and projections directly and are
arithmetically codable, but a full bi-interpretation requires a tree recursor,
tree coverage, equality reflection, and the logical translation. Their small
informal signature does not establish a smaller standalone checker. No
verified improvement of the repository's size envelope was obtained from this
route.

## Status

No new mathematical presentation strictly below the current complexity
envelope is certified by this independent audit. These notes are limitations
and research leads, not a substitute for a verified improvement.
