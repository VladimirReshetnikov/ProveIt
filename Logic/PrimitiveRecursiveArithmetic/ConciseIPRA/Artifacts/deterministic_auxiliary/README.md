# Deterministic auxiliary proofs for iPRA

Prepared for Vladimir Reshetnikov, 11 November 2026.

## Result

This package combines source-selected elimination and root-determined
introduction, while retaining unrestricted atomic progress formulas as
auxiliary intermediate formulas. For public guarded contexts and goals,
the new consequence relation is exactly the existing guarded/native one.
The public theory's ordinary realization is therefore bi-interpretable and
equiconsistent with full first-order iPRA. The number domains are whole,
equality is actual equality, and both numerical composites are the identity.

The comparison snapshot is ProveIt commit
`1517d9d79ce33f631e0f82960c849427cbba23bf`, under
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA`.

The result is a modest improvement in the repository's compact checker
convention. It is not an absolute minimality theorem or a new scalar
arithmetic foundation. The new compatibility theorem is a written proof;
it has not been formalized in Lean or Rocq.

## Start here

- `ipra_deterministic_auxiliary.pdf`: complete compiled report, including
  the new proof, measurement contract, verification, further research
  questions, and attributed inherited logical/arithmetic appendices.
- `ipra_deterministic_auxiliary.tex`: self-contained flattened TeX source.
- `paper.tex` and `theory/composition.tex`: modular authoring sources.
- `code/readable_checker.py`: annotated, standalone version.
- `code/checker.py`: direct 525-byte normalized compact implementation.
- `code/checker_bytes.py`: optional 522-byte parity-spelling profile.
- `code/checker_ast.py`, `code/checker_tokens.py`: separate coordinate profiles.
- `code/checker_strict.py`: standalone public-goal validator plus checker.
- `evidence/metrics.json`, `metrics.csv`, `test_results.json`: exact results.
- `tests/certificates/`: generated local/global certificates.
- `reference/PROVENANCE.json`: exact pinned source paths and Git blob hashes.
- `CLAIMS.json`: machine-readable statement of the result and its limits.
- `SHA256SUMS`: checksums of the released files, before any local rebuild.

## Measurements

Whole modules, normalized with `ast.unparse(ast.parse(source))` plus one LF,
under CPython 3.12.14. The shared runtime and standard JSON library follow
the baseline convention. Gzip-9 with `mtime=0` is informational only.

| Program | Significant tokens | AST nodes | Normalized bytes | Gzip-9 bytes |
|---|---:|---:|---:|---:|
| Direct compact | 265 | 303 | 525 | 331 |
| Optional byte profile | 265 | 303 | 522 | 329 |
| AST profile | 262 | 281 | 606 | 348 |
| Token profile | 258 | 287 | 571 | 339 |
| Strict public validator + checker | 491 | 563 | 1205 | 572 |

The compact coordinate envelope changes from **259 / 283 / 526** to
**258 / 281 / 522** (tokens / AST nodes / bytes), in different programs.
The mathematical composition alone gives the direct 525-byte profile;
replacing `not len(a) % 2` with `~len(a) % 2` saves the final three bytes.
The direct profile's gzip size is one byte larger than its 526-byte source
baseline; that increase is explicitly retained in the ledger.

### The public-goal contract matters

The compact profiles do not reject every noncanonical public statement.
Their exact theorem is soundness and completeness **for canonical guarded
goals**, allowing auxiliary intermediate formulas. They are not validators
of the public grammar. The strict profile supplies and counts that validator.

The strict checker improves the identical guarded-grammar control from
1208 to 1205 bytes and from 568 to 563 AST nodes. The older unrestricted
native strict control is 1109 bytes, so no global strict-checker record is
claimed. Nor is the complete auxiliary formula language claimed to have
the public theory's formula round trips.

## Reproduce

From this directory, with Python 3.12:

```sh
python3 reproduce.py
python3 code/checker_strict.py < tests/certificates/zero_symmetry_all_numbers_local.json
python3 -O code/checker_strict.py < tests/certificates/zero_symmetry_all_numbers_local.json
```

The main reproduction run verifies 33 pinned reference files, regenerates
26 certificates for 13 examples, and executes 242 command-line checks.
All passed in the recorded environment. A successful checker run exits
normally and prints exactly `ACCEPT`; an exception is rejection.

The token profile needs `*_global.json` packets; the other profiles use
`*_local.json`. The strict profile rejects the administrative-only Q goal,
even though its auxiliary proof is sound and accepted by compact profiles.

Proof generation is untrusted. The checkers do not import the producers,
normalizer, this reproduction script, or any theorem database. The vendor
modules are frozen reference sources; `tests/generate.py` changes the
derived numerical-cases construction to use atomic progress with an unused
induction hypothesis. Its audits reject forbidden zero-source transports,
atomic case introductions, and compound progress introductions in positive
generated proofs.

## Compile the document

With a normal LaTeX installation including the listed standard packages:

```sh
python3 build.py
```

This rebuilds the self-contained TeX and compiles it twice. Alternatively:

```sh
pdflatex -interaction=nonstopmode -halt-on-error ipra_deterministic_auxiliary.tex
pdflatex -interaction=nonstopmode -halt-on-error ipra_deterministic_auxiliary.tex
```

The flattened source does not need the modular TeX or external code files.
`python3 build.py --source-only` regenerates it without invoking LaTeX.

## Mathematical scope and the crucial obstruction

Auxiliary equation induction is available before equality is repaired.
It gives equation cases, so the numerical zero-source symmetry proof can
be replayed. After numerical equality is restored, transport through public
guarded formulas is recovered separately. Soundness uses a progressive
reading for an auxiliary atomic D and the conditional reading for a
compound D; these readings agree with the ordinary reading on public goals.

If all intermediate matrices are forced to be guarded, the combination
fails: a counterinterpretation makes every bare equation `0=t` true and
other equations actual equalities. It validates the restricted canonical
rules but invalidates `0=1` implying `1=0`. Thus the auxiliary formulas are
essential, rather than a removable expositional device.

The archived Lean files are selected existing source snapshots, not a new
Lean formalization or a standalone Lake project. The pinned repository's
Lean development was not rebuilt during this investigation.

## Attribution

The source-dispatch reduction, guarded grammar, scalar predecessor,
equality reflection, primitive-recursive compiler, and arity decoder are
inherited from ProveIt. Exact copied files retain their Git blob hashes.
ProveIt's MIT No Attribution license is in `reference/LICENSE.txt`.
The new contribution is the compatibility proof with its public/auxiliary
boundary, the combined implementations, their documentation, and the
reproduction/audit artifacts. The report contains further research questions.
