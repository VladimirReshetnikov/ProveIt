# PA195 diagonal-freshness prerequisite

The diagonal calculus uses the numeric code `4 * Cantor(a,b) + tag` for
formula constructors. `PA195FreshBound.candidate_pra_fieldBound` is a Lean
proof of an actual theorem of candidate classical PRA: if that code is
positive, each of its two decoded Cantor fields is strictly smaller than the
code. The statement uses the bounded arithmetic graph of the literal Cantor
pairing, not Foundation's distinct pairing convention. Its model proof holds
in every model of IOpen, hence in every candidate-PRA model, including
nonstandard models; first-order completeness supplies the PRA derivation.

This proves only the immediate-field bound. It does not yet encode the
recursive occurrence predicate, prove the code is absent from its own decoded
formula, verify any generated proof template, or connect a PA refutation to
PA195 halting. The arithmetic needed to verify a primitive-recursive generator
must be distinguished from the possibly unrestricted PA induction instance
that generator inserts inside a PA proof.

To check from the repository root, set `IPRA_LEAN_OVERLAY` to the matching
audited project object directory and `IPRA_FOUNDATION_OVERLAY` to the matching
Foundation object directory, then run:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check.sh
```

The script verifies source and direct object hashes and rejects `sorryAx` in
the printed theorem dependencies. It uses the supplied audited object
directories; it does not rebuild their transitive dependencies.

`PA195DecodedFields.candidate_pra_decodedFieldBound` strengthens this to the
actual first decoder step: it uses the bounded graph for `p = n / 4`, then
the Cantor graph for its two components, and proves that both components are
strictly less than every positive `n`. Its supporting semantic theorem holds
for arbitrary IOpen model elements. Check this extension, including a fresh
build of `PA195FreshBound.olean`, with the same overlay variables:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-decoded.sh
```

This still proves only one decoder step, not represented recursive occurrence
or self-freshness.

`PA195PathBound.lean` proves an all-model path-descent result using candidate
PRA's open induction. For a supplied binary primitive-recursive function code
and seed, its values must describe a path whose intermediate nodes are positive
and whose next node is one of the two Cantor fields of the current node divided
by four. For an arbitrary, potentially nonstandard model-length limit, the
result bounds every visited node by the root and shows that every field of a
visited positive node is strictly below the root. `path_self_fresh` states
this as absence of the root from an explicitly defined path-occurrence
over-approximation.

The function code and its step equations are explicit hypotheses. The actual
PA195 recursive occurrence predicate and a path extractor connecting it to
the supplied code have not yet been defined or proved correct, so this is
not yet full self-freshness or a syntactic PRA theorem about that predicate.
To check the path result and rebuild both earlier calibration modules, use:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-path.sh
```

`PA195OccursFormula.lean` represents the path-occurrence over-approximation and
its positive-child step premise as explicit formulas of the candidate-PRA
language. For each **fixed** binary primitive-recursive path code `f`,
`candidate_pra_represented_path_fresh` proves the universally closed
conditional as an actual candidate-PRA theorem: if the represented path
obeys the represented step condition, its root does not occur as a Cantor
field on that path. The semantics of both formulas are checked in every
candidate-PRA model, including nonstandard ones. The fixed `f` is a theorem
parameter, not an internal quantifier over function codes.

The same four-tag decoder and diagonal clause are used by PA194. This
represented predicate remains an over-approximation for a *supplied* path;
no extractor has yet been shown to turn an arbitrary PA194 decoder
occurrence into such a path, so the theorem does not establish complete
self-freshness of the PA194 decoder. To check the representation and PRA
theorem using the same audited overlays, run:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-occurs.sh
```

`PA194ChildCodes.lean` uses candidate-PRA bounded witnessing to prove the
existence of a primitive-recursive function code for each of the exact two
PA194 decoder-child functions, `first(n / 4)` and `second(n / 4)`, together
with candidate-PRA proofs of their represented graph instances. The model
lemmas confirm those code values in every candidate-PRA model. These witness
codes are existentially supplied by Lean; an explicit serialized code is not
exported. A branch-choice iterator and the connection from arbitrary actual
decoder occurrences to such a path remain to be constructed.

To check the child-code results and freshly build their two earlier
prerequisites, use the same audited overlays and run:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-child.sh
```

`PA194PathZero.lean` removes the earlier positive-intermediate-node assumption:
both decoder children are at most the parent even for code zero, so model-length
child paths remain bounded through the truth-code case. Occurrence still
requires its visited node to be positive.

`PA194PathIterator.lean` explicitly constructs a primitive-recursive path
code from supplied root and branch-choice codes and the two child witness
codes. Given candidate-PRA graph proofs for those child codes, its model-step
theorem shows that each step chooses one of the exact decoder fields in every
candidate-PRA model. It does not require the branch selector to be Boolean:
zero chooses the second child and any nonzero value chooses the first. The
resulting path self-freshness theorem allows nonstandard model-length limits
and needs no positive-intermediate-node premise. Root and choice codes and
child-graph proofs are explicit parameters; the final extractor from arbitrary
actual decoder occurrences into those choices remains unproved.

To check these results and freshly rebuild their dependencies, run:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-iterator.sh
```

`PA194BranchSeed.lean` constructs the parameter interface for the branch
iterator. Candidate PRA supplies existential primitive-recursive witness codes
for both projections of an auxiliary seed pair and a Boolean branch-word bit
reader. In every candidate-PRA model, the seed packs a root and branch word;
the path starts at that root and its next exact decoder child is determined by
the branch-word bit at each index, including nonstandard indices. The
auxiliary seed uses Foundation's pairing; PA194 formula codes still use the
distinct Cantor pairing. The witness codes are not serialized.

This interface does not yet prove that an arbitrary occurrence in the actual
PA194 recursive decoder supplies a suitable branch word, nor does it prove a
consistency or halting implication. To check it with the same audited overlays
and fresh local prerequisite builds, run:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-branch.sh
```

`PA194StrongInduction.lean` derives strong induction for any fixed binary PR
code in every candidate-PRA model, using bounded induction. The companion
`PA194OccurrenceStrong.lean` proves self-freshness without constructing a
branch-word path: for a supplied binary PR occurrence code, it assumes that
any nonzero occurrence result at `(n, v)` comes from a positive `n` and is
explained by one of the two immediate Cantor fields of `n / 4`, or by a
nonzero occurrence result at one of those children. Under that uniform
one-step coverage hypothesis, every reported label is below its code, so the
code cannot occur in itself, including at nonstandard model elements.

This theorem still assumes the occurrence code and its all-model coverage
property. It does not construct PA194's actual occurrence code or establish
that property for it. Check the bounded-strong-induction route using:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-strong.sh
```

`PA194PackedDescent.lean` proves an actual candidate-PRA theorem that packages
a formula code and candidate label using an auxiliary Foundation pair. For a
positive PA194 formula code, pairing either exact quotient/Cantor child with
the same label gives a strictly smaller index. This is a rank ingredient for
an occurrence fixpoint; it does not construct the occurrence code or prove
its recursion-coverage property. The auxiliary Foundation pair is distinct
from the Cantor pair used by the PA194 decoder.

Check the theorem and freshly rebuild its calibration prerequisites with:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-packed.sh
```
