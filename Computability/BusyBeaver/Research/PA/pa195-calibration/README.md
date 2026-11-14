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
