# Can all raw trees become the public formula language?

## Result

Not with the existing acceptance relation and its zero-padding native reading.
Soundness for all successful raw runs and completeness for the canonical
encoder image do **not** imply completeness for every raw spelling. There is
a proven obstruction even among sorted, scoped integer/list goals, so merely
enlarging the declared public grammar cannot close this gap.

A quotient or theorem-enumeration interface is mathematically coherent. It is
a different interface from checking a proof of a separately supplied raw goal.
To implement the latter, the trusted code must canonicalize/compare decoded
conclusions (or check a proof of their identification); those operations must
be counted.

## Exact statements

Let `R` be raw integer/list trees; let `L` be the native formula language; let
`delta : R -> L` be a specified ordinary reading, where defined, and let
`eta : L -> R` be the canonical encoder. Write `C(a,p)` for successful finite
execution with declared root `a` and proof payload `p`.

The existing results have the form

1. `C(a,p)` implies `T |- delta(a)`.
2. `T |- A` implies `C(eta(A),p)` for some `p`.
3. `delta(eta(A)) = A`, or the specified native/guarded equivalent of `A`.

The proposed stronger raw-public contract would require

4. For every raw public `a`, `T |- delta(a)` implies `C(a,p)` for some `p`.

Statement 4 is false. It is not a consequence of statements 1--3. The reverse
formula round trip for a raw-formula presentation cannot be justified merely
by the canonical identity in statement 3.

## The second-padding-slot obstruction

In the uniform-zero-1 encoding, consider

```text
[[5],[1]]
```

The old sorted public grammar accepts this closed equation. Its standard
reading is `S(0)=S(0)`, because the occurrence `5` refers to the second dummy
slot beneath the left successor, and dummy slots are read as zero.

The repository proves a parametric soundness invariant: the same checker is
sound if the **second successor dummy slot** is instead interpreted as an
arbitrary fixed parameter `c`, while the first successor dummy and every
iterator padding slot remain zero. Under this modified reading the displayed
goal is `S(c)=S(0)`, false at `c=1`. Therefore no certificate for the displayed
raw root can be accepted. The original zero-0 spelling is `[[5],[0]]`; in the
later shifted codec it is `[[7],[1]]`.

This is a mathematical invariant of all accepting runs, not a bounded failed
search. The key computation fact is that a recursively validated predecessor
cannot reach the newly introduced second successor padding slot: it is
exactly at the excluded upper scope bound. A state-independent update may
avoid checking that predecessor, but its successor computation is then
independent of the predecessor's value. All logical and substitution rules
preserve the modified reading.

Source at the pinned commit:
`Artifacts/composition_and_dummy_slots/proofs/second_dummy_proof.md` and
`proofs/independent_second_dummy_proof.md`. The new incoming packages expressly
retain this caveat for sorted-only checkers and either validate actual binding
or fuse a forbidden-slot mask to obtain exact public syntax.

## An easier obstruction when literally every raw tree is public

The ordinary raw reading declares any formula array of arity at least four
to be `0=0`; its children are annotations with no formula reading. Nevertheless
the opener traverses the children, and an invalid annotation can force failure
at the initial scope check. In the unshifted `token239.py` codec,
`[1,0,0,0]` has formula reading `0=0`, but the initial root opening visits
its first child at depth 1. Scalar 1 is out of range and invokes the missing
image; the opening fails independently of the proof payload.

Thus all-raw completeness fails even before the more informative scoped
padding example is used. Giving previously out-of-scope term leaves a default
zero reading would generate yet more such true-but-uncheckable aliases.

## What quotient syntax does and does not achieve

Define `a ~ b` when the chosen decoders produce the same native formula,
`delta(a)=delta(b)`. The quotient language `R/~`, restricted to decoded native
formulas, is essentially a second presentation of the native language. Define
the quotient proof relation by

```text
Q([a], (b,p)) iff delta(b)=delta(a) and C(b,p).
```

Then statements 1--3 give soundness and completeness of `Q`: for the reverse
direction choose `b=eta(delta(a))`. On this syntax the raw aliases disappear
as distinct formulas, so the canonical round trip is identity on quotient
classes. Composing with the native/iPRA bridge retains whole numerical
domains, actual equality, and the numerical identity graph.

The equality comparison in `Q` is additional trusted work. Omitting it permits
a certificate for an unrelated theorem to be asserted as a proof of any raw
goal. Treating class representatives as if literal raw equality tested their
classes is contradicted by the padding example. A canonicalizing frontend can
instead compute `N=eta o delta` and invoke `C(N(a),p)`; again `N` is part of
the complete checked interface.

This is a syntactic-decoding quotient. Quotienting by *provable equivalence*
instead would require an additional proof relation rather than a generally
decidable parser comparison and should not be silently substituted.

## The legitimate theorem-enumerator alternative

One can regard `a` as an internal component of a proof object, rather than a
separately declared formula to be checked. Assign every successful proof object
the conclusion `delta(a)`. Statements 1--3 then imply that the set of decoded
conclusions is exactly the native theorem set. That is a valid proof-enumeration
presentation, with no requirement that every alias of a theorem be usable as
the internal representative.

This distinction must be explicit. It does not establish statement 4, and it
does not by itself make an ACCEPT-only program a standalone producer of a
canonical conclusion. If the advertised tool prints native syntax, its decoder
is trusted output computation and is part of the measured program. If the
advertised output is an abstract class, the interface is weaker/different
from the repository's exact canonical public-goal interface; compare like
contracts, not only source counts.

There is already prior art in the incoming
`ipra_shared_witness_bundles_2026-11-13.zip`, directory `synthesis/`.
`NOTE.txt` states the syntax, all eight proof constructors, substitution lemma,
soundness invariant, and canonical-completeness compiler for an actual
standalone theorem synthesizer. It consumes one JSON proof tree and prints a
canonical Eq/Q/D formula. It measures 875 significant tokens / 1,027 AST nodes
/ 2,145 normalized bytes. Typing of supplied witnesses, matrices and iterator
bodies remains necessary. The older `prevalidated_elimination` synthesis
experiments (330/390/951 and 334/392/777) are explicitly **not established as
complete checkers** in the article.

## What a correct canonicalizer must do

A normalizer for the zero-padding raw reading needs more than the existing
scope floor. It must distinguish real and dummy slots, erase annotation
subtrees that the reading ignores, turn scalar/arity aliases into the chosen
native constructors, and treat formula versus term positions differently.
One recursive implementation can carry a stack or a bit mask of slot meanings:
successor adds two unavailable slots; iterator counter/initializer one
unavailable slot; iterator update one available slot; `D` two available slots;
`Q` one available slot. A leaf selecting an unavailable slot normalizes to zero.
This is close to the already delivered forbidden-slot-mask machinery, except
it rewrites aliases instead of rejecting them.

It could be useful to fuse that normalizer with the initial opening, but no
shorter complete implementation or equivalence proof has been obtained here.
There is no established theorem that it can be omitted or charged to an
untrusted input generator for a supplied-raw-goal interface.

## Source locations in the article

- `ch11_cert.tex`, `cert:def:reading`: sorted raw reading, dummy slots, annotations.
- `cert:lem:opening`: opening preserves the reading on successful validations;
  annotations can add rejection despite having no reading.
- `cert:thm:base-sound`: soundness for successful raw runs.
- `cert:thm:base-complete`: completeness through canonical encoding.
- `cert:rem:imported`: guarded public equivalence and the auxiliary progressive
  reading of an atomic `D` matrix. Arbitrary raw extension must specify which
  reading it uses; the guarded equivalence cannot be assumed for all auxiliaries.
- `cert:def:contracts`: raw, goal, and typed contracts are distinct.
- Further question “Readings modulo annotations”: quotient/idempotence issues
  are already recognized as research questions, not solved public completeness.

Assessment: the quotient observation is valid mathematics, but it supplies no
honest zero-cost solution of the requested stronger raw-alias contract and is
not a new arithmetic axiomatization.
