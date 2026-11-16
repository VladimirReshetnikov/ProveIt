# Native Clause Programs for iPRA

A general proof-producing framework for embedding finitary mathematical
concepts and arguments into intuitionistic primitive recursive arithmetic.

The central proposal is to use ProveIt's checked five-rule native clause
calculus `KPrf` as the intermediate representation for finite proof graphs:

- local proof nodes carry actual `KPrf` or `Prf PRAAx` derivations;
- graph composition is `KPrf.cut`;
- specialization is `KPrf.subst`;
- terminal native proofs export through `KPrf.toNPrf` and
  `native_iff_pra`;
- direct algebraic theorems from the new checked `IPRADerivations` library can
  be imported through `pra_iff_native` and `kprf_iff_nprf`.

## Main files

- `paper/native_clause_framework.pdf` - 64-page full report, compiled and visually inspected.
- `paper/native_clause_framework.tex` and `paper/sections/*.tex` - LaTeX source.
- `lean/NativeClauseFramework/Bridge.lean` - candidate bridge/list-cut code,
  with no proof holes, not compiled here.
- `lean/NativeClauseFramework/*Blueprint.lean` - dependency-ordered Lean
  outline with 17 explicit `sorry` lines.
- `lean/FORMALIZATION_PLAN.md` - exact path to a checked implementation.
- `code/native_clause_framework.py` - exact finite reference algorithms.
- `code/test_native_clause_framework.py` - fourteen regression tests.
- `examples/example_run.json` - generated demand/relational example.
- `metadata/THEOREM_LEDGER.md` - claim-by-claim status.
- `metadata/DIFFICULTY_MATRIX.csv` - recurring difficulties and endpoints.
- `metadata/SOURCE_AUDIT.md` - pinned repository source audit.
- `schema/native_clause_program.schema.json` - machine-readable graph metadata
  schema.
- `validation/` - tests, static audit, PDF metadata, and QA records.

## Source pin

Research was pinned to:

```
VladimirReshetnikov/ProveIt
8649990597d73657bde480b6c389de7f85bc0cb0
```

The repository was changing rapidly, so the exact pin matters.

## Formal status

No Lean executable was available in the artifact runtime.  No new Lean theorem
in this archive is claimed kernel-checked.  The report distinguishes:

1. upstream checked declarations;
2. complete human proofs;
3. exact executable evidence;
4. uncompiled Lean candidates;
5. Lean blueprints;
6. conditional application-specific producer obligations.

Python tests are evidence for finite algorithms only and are not iPRA proofs.

## Rebuild and verify

From the package root:

```sh
python3 verify.py
./build.sh
```

`build.sh` runs the Python tests, regenerates the demo, compiles the PDF,
records PDF information and preflight output, and refreshes `MANIFEST.sha256`.
It does not download dependencies or modify the ProveIt repository.

To check the Lean sources, copy them into the pinned ProveIt workspace as
described in `lean/FORMALIZATION_PLAN.md`, then use that repository's Lean/Lake
toolchain.
