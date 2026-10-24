# Centered scalar carriers: twelve unrestricted integers

Two complete new polynomial equations are supplied as literal integer
arithmetic DAGs. The final output of the chosen JSON file is set equal to zero.

| File | Variables/domain | Operations | Exact degree |
|---|---|---:|---:|
| `integral_centered.json` | 12, all integers |143|1200|
| `rational_centered.json` | 12, all integers |146|1184|

The first saves two operations against the pinned rational 145/1200
equation. The second lowers the degree by sixteen at one extra operation.
The old integral 141/1456 option is retained under `parent/`.

`PROOF.md` contains complete formulas, the universal polynomial shears,
their inverses, exact attained degree proofs, and the inherited-calibration
boundary. These are incremental applications of norm centering to the
current scalar carrier; global novelty or minimality is not asserted.

The exact coherent six-port source34 tuple is included under `coefficients/`.
All four large values are rebuilt by the retained finite recipe from the
supplied literal machine and complete 943-tile table; the two cone values
are powers of two. The recipe is compared against every payload byte.
The original parent proof and its named arithmetic dependencies are kept
under `parent/`. No parent file has been mathematically edited.

Run, from this directory or with corresponding paths from elsewhere:

```sh
python3 -B build.py --check
python3 -B verify.py --output CHECKS.json
python3 -B -O verify.py --output CHECKS_OPTIMIZED.json
```

Only the Python standard library is needed. Omitting `--check` regenerates
the two JSON circuits. The new checker imports no producer. It reuses the
retained independent free-polynomial norm oracle and prefix checker, with
the new center formula supplied explicitly.

AI assistance: the new reductions, explanation, builders, and review were
prepared with OpenAI ChatGPT. The parent material and native construction
are credited to the pinned ProveIt sources. The retained upstream licence
is `parent/source/LICENSE.UPSTREAM` (MIT No Attribution).
