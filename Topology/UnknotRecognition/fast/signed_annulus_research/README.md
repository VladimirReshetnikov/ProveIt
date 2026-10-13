# Signed primitive annuli: native regression fixture

The embedded fixture comes from the `finite_figureEight` record, standard
vertex surface 71, in report 57's discovery bank at repository revision
`e0b2f802f336fcb51e9ec5f29174cfe28dfb9d39`. It uses 10 tetrahedra and 30 normal
disks. The exact triangulation, normal coordinates, source JSON hash, and
expected outcomes are in `corpus.json`.

The same bank supplies further fixtures in the `finite_figureEight_interior`
record. These require the established source-certified two/three-handle
reduction before the signed criterion. Both the ordinary and top-reduced
certificate schemas are checked independently. A retained-refusal fixture
has transported curve `x^5 y^2`; coprime exponent sums alone do not certify
free-group primitivity.

The existing geometric core certificate succeeds. Two remaining annuli have
source words `z x^-1 y^-1` and `z^-1 y^-1 x^-1 y`, where the certified core
cancellation kills `z`. Their conjugacy classes become `x^-1 y^-1` and
`x^-1`; one common automorphism carries these to distinct free generators.
The old unsigned primitive-family and whole-cut kernel criteria refuse this
input. The maintained default signed phase certifies two genus-two handlebodies
after earlier methods refuse. Set `annulus_method='counts'` to disable that
phase. Source and boundary queries are shared across all attempts.

This is a terminal census for a supplied normal cut. It is not a verdict that
the figure-eight knot is trivial, and it does not construct the global
quasipolynomial unknot-recognition hierarchy.

From `fast/`, run:

```bash
python -m signed_annulus_research.reproduce --output /tmp/signed-annulus-replay --regina
python -m unittest tests.test_cyclic_basis tests.test_signed_annulus_source tests.test_signed_annulus_integration -v
```

The first command exports the full authenticated certificate and an audit
JSON. The optional `--regina` flag independently constructs the actual cut
triangulation and recognises its handlebody components. The historical bank
hash is checked when the report 57 source is present; the embedded fixture is
otherwise sufficient for replay.

The public entry point retains `annulus_method='counts'` by default. Enable
the new conservative fallback with `annulus_method='signed_rank_two'`.

## Regression environment

The complete upstream test suite additionally uses the repository's report
and synthesis fixtures. Its transitive dependencies include
`Topology/UnknotRecognition/synthesis/data/cocycle-reuse-audit.json`, loaded
by the existing transport-annulus tests. One frozen-output comparison also
reads commit `1aeabfa735c78a30b732405b101009d376d56f18` from Git history. A
shallow or sparse checkout must retain these inputs. They are not needed by
the embedded five-case reproduction above.

The final full regression run passed 1,733 tests and 1,750 subtests in 506.68
seconds. Eight further tests were blocked at setup because that transitive
fixture had been excluded while narrowing the isolated checkout. After
restoring its exact pinned contents, all eight passed in 0.99 seconds. Thus
all 1,741 collected tests passed across the full run and its targeted rerun.
The supplied regression audit preserves the logs and explains the earlier
disk-space failures, missing historical commit, and two pre-existing stale
forest expectations. Those historical refusal assertions now explicitly
select `lower_forest='source'`; the production default remains unchanged.
