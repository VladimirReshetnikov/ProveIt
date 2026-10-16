# Machine audit and a 250-state research candidate

This folder contains the executable companions for the report. The repository
snapshot is pinned at ProveIt commit
`17d0f2eaa650901cda59764dfcc4661c199e49c8` (16 October 2026). The source manifest
contains 12 files totaling 140,046 bytes. The download helper fetches these
exact public files, checks their SHA-256 hashes, and only then executes the
small compiler backend. The original repository is never changed.

## Result and scope

The existing 252-state route is reproduced exactly. A bounded search of
9,216 choices additionally commutes the five internal derived-conjunction
occurrences in the container and collection formulas. Its minimum is 250
working states. The selected candidate swaps the order of transitivity and
power bounding in the container clause, swaps coverage and support in
collection, and reassociates the outer bundle to `(V AND C) AND G`.

These changes preserve formula semantics: the relative conjunction used by
the machine is `And_F(A,B) = ((A -> (B -> F)) -> F)`, whose Boolean value is
`F OR (A AND B)`. Its commutativity and associativity require no assumption
that F is false. No variable or binder is moved across another binder.

The output has 188 decision states plus the unchanged 62 framework states.
Its normalized binary table has 500 transitions, start 0 and halt target 250.
This is a research candidate whose complete Con(ZFC) endpoint is unproved.
The accompanying report establishes the ordinary first-order source theory's
consistency calibration using two-sided membership twins. The exact reduced
Hilbert calculus, its relative falsity and dynamic-binder behavior, proof
search, and compiler simulation still require proofs. These are separate
layers: the mathematical source-theory result does not certify the table.

## Run

Use Python 3.10 or newer. From this directory:

```sh
python3 reproduce.py
```

The default reproduces both the baseline diagnostics and the fixed candidate,
including the one-million-step operational prefixes, but does not repeat
either combinatorial search. After the sources have been fetched, no network
is needed:

```sh
python3 reproduce.py --offline --search-orders
```

That exact command was tested successfully in this session. To repeat the
full 9,216-case conjunction search as well, append `--search-conjunctions`.
The recorded full search took 144 seconds. The original 288-case outer
order/grouping search is enabled by `--search-orders`.

For the fixed 250-state table alone after source fetch:

```sh
python3 generate_candidate250.py
```

The generator checks both frozen hashes and never substitutes a merely
same-sized table. Generated machine outputs remain in this directory.

## Frozen hashes

`conjunction-candidate-250.named.tm`:

```text
799ec421e41533229cb24aa172f61fc637d3435466d8d0f2eff0fcadf2cdcfc6
```

`conjunction-candidate-250.tm`:

```text
d7af3920268db1c95bf71dc06b77e53c8266086a13043b2fc91f9319c520aff1
```

## Important evidence

- `conjunction-search-results.json`: the cost distribution across all 9,216
  choices, the minimum, and both minimizers.
- `conjunction-candidate-250-recipe.json`: exact formula ASTs, macro program,
  commutations, and selected order/grouping.
- `candidate250-generation.json`: exact regeneration and normalization result.
- `candidate250-normalization.json`: seven normalizer regressions and the
  conservative state audit.
- `candidate250-audit.json`: the complete-table audit and finite prefix.
- `independent_backend.json`: exact reproduction of all eight older backend
  variants and the 288-case outer-order search.
- `independent_252_audit.json`: independent verification of the pinned 252
  table, graph and one-million-step prefix.
- `base3_codec.py` and `base3-codec-results.json`: a finite implementation of
  the report's canonical finite decoding of all natural formula codes.
- `translation_comparator.py` and `twosided-Delta-control-results.json`:
  a 348-state compiler control retaining all eight original logical rows
  with every equality replaced by two-sided twins and a computed fresh binder.
- `STATUS.json`: a layer-by-layer statement of what is and is not established.

The conservative audit finds all 250 states reachable and no exact quotient
or radius-four local merge. Those outcomes are not a minimality proof.
The one-million-step prefix never validates the edited AX emission routine,
and nonhalting of a finite prefix proves no consistency statement.

The pinned auditor's verbatim normalization JSON retains its original
`theory_calibration_status` string, which predates the report's new source
theory proof. `STATUS.json` gives the current layered interpretation. Neither
the old status nor the new ordinary-FOL theorem is an endpoint certificate.

To regenerate the translated-equality compiler control after source fetch:

```sh
python3 translation_comparator.py
```

Its fresh local binder for Delta(i,j) is `k=3P(i,j)+1`, computed by the
already present membership constructor. The strict inequality `k>i,j` means
that no extra register instruction or freshness filter is required. It costs
348 states, and no larger-family optimality or compiler correctness theorem
is asserted. This control preserves the original logical-row set rather than
silently assuming the smaller row set is complete.

## Attribution

Mira-Cult designed the original machine and container/collection calculus.
Jeff's published verification snapshot supplies the imported finite program
and its specifications. Andrew James Wade wrote the public `TMBuilder`
backend, whose retained license is MIT-0. This work adds the internal
conjunction search, its selected source rewrite, fixed regeneration, and the
canonical truth-code normalization note. Upstream material is fetched from
its exact existing source locations and is not relicensed by this package.
