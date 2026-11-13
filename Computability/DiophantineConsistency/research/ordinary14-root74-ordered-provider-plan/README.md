# Root74 slim overlay: ordered lexical provider plan

This is a **candidate plan**, not a Lean build, a provider-coherence
certificate, or permission to launch a build. `plan.json` gives one concrete
order and records each candidate stage's source, source hash and imported names
as recorded by the pinned slim-overlay lexical inventory. It records the
current path, resolved path and SHA-256 of each of the 31 project frontier
objects and four external objects in the previously reviewed bounded survey.
There are 162 proposed stages: three qualified source candidates followed by
159 inert-overlay draft modules. The last is `Root74Endpoint`. This order is
topological **with respect to the inventoried import headers and that frontier
only**. It is neither a complete Lean dependency order nor evidence that any
stage will elaborate.

An [independent review](../../reviews/ordinary14-root74-ordered-provider-plan-independent/README.md)
checks the actual simple source headers, lexical endpoint ancestry and
observed object hashes, within the same bounded scope.

Reproduce the point-in-time observation from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary14-root74-ordered-provider-plan/check.py | cmp - Computability/DiophantineConsistency/research/ordinary14-root74-ordered-provider-plan/plan.json
```

The program only reads and prints, never invokes Lean, and does not materialize
sources. It pins the previous slim inventory and survey, checks the bytes of
all 162 candidate source files, checks the proposed order against their
previously inventoried imports, hashes the 31 current frontier objects and
compares the four external objects with the survey. It **does not independently
parse the headers**, authenticate all recorded object hashes against producer
receipts, recursively follow those objects' imports, check companions or
collision freedom, reserve resources, or guarantee the observed files remain
unchanged. The pinned survey's external files and the retained `/tmp` roots
must exist to reproduce the exact receipt. A mismatch is a reason to inspect,
not to silently replace the pinned evidence.

## Observed cut and proposed stages

The qualified-source stages are, in this valid lexical order:

1. `DiophantineConsistency.DiscreteOrderedRingFacts`: imports
   `Mathlib.Data.ZMod.Basic`, `Mathlib.Tactic.Linarith` and
   `Mathlib.Tactic.Ring`.
2. `DiophantineConsistency.Compact44.FreeJ13`: imports the observed frontier
   objects `FreeJSumSquares` and `FreeJSignedTransport`, plus
   `Mathlib.Tactic.LinearCombination`.
3. `DiophantineConsistency.Compact44.FreeJ13Halt`: imports stage 2 and the
   observed `FreeJGraphAuxiliary` and `QCube92Halt` frontier objects.

Then follow the 159 `bare-inert-overlay` stages in `plan.json`, in their
recorded order. They start with `P75NegativePell` and `P74PositiveGuard` and
end with `Quotient88PositiveBridge`, `Root78PositiveBridge`,
`Root74PositiveBridge`, `Root74Endpoint`. The `.lean.src` paths are inert
snapshots; materializing them as `.lean` files is a future operation, not
something this plan has done. The complete per-stage import lists and hashes
are in the JSON, avoiding an abbreviated list that might be mistaken for the
whole lexical candidate sequence.

The selected project frontier is
`/tmp/p72-current-base-extension-attempt02-20261105/lib`, whose sampled 31
frontier paths resolve to 24 files under that tree and seven files under
`/tmp/current14-standard-fresh-build-20261104/lib`. The four sampled external
paths are under `/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib` and
resolve into an existing Mathlib build; their exact paths and hashes are in
the JSON. The selected Lean toolchain's library is
`/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean`.
The survey checked selected producer records and guard slots, but that is not
proof that every frontier object or package dependency has compatible
transitive provenance. The failed P72 retry roots must not be mixed into the
selected route: their same-source `ModelDifferenceRing` objects differ.

## Work needed before a guarded build

1. Revalidate the selected P72 and linked-base producer records and all
   required companions, source identities, transitive imports, package and
   runtime dependencies for every frontier object, using immutable or protected
   evidence. Enumerate and reject missing, ambiguous or unrecorded producers,
   alternate search candidates and companion files. The present inventory is
   a bounded lexical cut, not a complete object-closure search. Establish how
   Lean actually searches package and core Init files; the survey found the
   package `Init.ilean` absent while the core file exists.
2. Design an exact ordered search-path and isolated source/output layout,
   including the two project provider roots, package and toolchain, and prove
   expected path/realpath/hash/companion resolution for each input and stage.
   A plausible intention is a fresh output root preceding the selected P72
   and package roots, but the actual Lean search semantics and base-link
   behavior remain unverified. No command here asserts a valid `LEAN_PATH`.
   Enumerate alternate names and implicit/dynamic imports, not just the 162
   stage names. Review an executable, fail-closed runner independently before
   materialization or launch; none is supplied by this packet.
3. Secure the externally coordinated exclusive Lean slot and observe the
   established guard: `/tmp` available bytes strictly greater than
   5,100,000,000, host available memory at least 10 GiB, stop at sampled
   session RSS of 4 GiB, 180 seconds per child, six hours per run and 0.2
   second sampling. Independently validate descendant monitoring and error
   handling. Preserve all existing roots and evidence; sample checks alone
   neither reserve space nor exclude concurrent uncoordinated processes.
4. Once the previous conditions hold, create fresh isolated source and output
   roots, verify the materialized bytes against the pinned source hashes, and
   check absent or explicitly accounted-for output and companion names. Run
   guarded `lean --deps` before each sequential compile; compare actual
   resolutions against the approved plan. Unexpected dependencies, search
   paths, changed inputs, monitoring errors, or missing outputs must stop the
   run rather than trigger fallback. Retain per-stage commands, exit status,
   resolved inputs and companions, hashes, resource samples, output hashes and
   postflight checks, and independently review the completed chain.
5. Capture and inspect the endpoint's three `#print axioms` results and its
   derivability statements, with the completed coherent provider evidence.
   The symbolic endpoint concerns the shifted expression and mapped native
   refutation. Further binding of symbolic ports and expression to the actual
   equation bytes and PDF is still required for the displayed physical
   equation. Neither this plan nor the external 74-operation count proves
   the internal equivalence.

The candidate sequence could change after actual guarded dependency
resolution or a source fix. Revisit and independently review the entire
affected order and provider closure if it does. This plan makes no claim of
minimal stages, completeness, proof existence in iPRA, or correctness of the
physical equation.
