# Suggested C2 update (not applied)

The following is a proposed update for review, not a change made to ProveIt.

## C2: least Turing degrees in effective-dense classes

**Negative answer supplied by a new conventional proof draft; not yet
independently refereed or Lean-checked. Priority remains unverified.**

For every 1-generic G that computes no eventually different function, the
uniform and nonuniform effective-dense classes of G lack a representative
of least ordinary Turing degree. In particular this holds for all
2-generics and, using the classical Kjos-Hanssen--Merkle--Stephan theorem,
all non-high 1-generics. Low Delta-2 binary counterexamples therefore exist.

The original gap is bypassed as follows. A null omission set S computable
from G yields a bounded least-missing-offset function on sufficiently long
blocks. An infinitely often computable agreement produces a decidable
one-point-per-block selector escaping S. An effective-dense description
computed from the erased oracle would correctly predict G on infinitely
many of those erased coordinates, contrary to 1-genericity.

The result can enforce any unbounded computable every-prefix disagreement
budget. It also supplies a descending chain in the uniform class without
a lower bound belonging to the full nonuniform class, as well as exact
finite meets and finite Boolean patterns of ordinary degrees. Every
representative in these constructions can lie below a fixed low generic.

## Retain as separate questions

The high 1-generic case; minimal elements of the full class; arbitrary
countable coinitiality; the exact common lower cone of all computable-null
erasures; and c.e. binary counterexamples are not settled in the draft.
These are follow-up questions raised by the work, with literature status
to be independently checked rather than automatically labelled open.

## Review before merging

Audit the computable selector lemma, the full-class quantifiers, the
nonuniform total-function listing in the packed chain, and the explicit
classical dependency of the low refinement. The companion finite tests
check finite invariants only and cannot replace that mathematical review.
