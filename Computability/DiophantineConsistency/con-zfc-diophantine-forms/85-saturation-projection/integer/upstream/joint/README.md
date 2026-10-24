# Exact joint positivity and polynomial projections

The final unrestricted-integer variable/degree endpoints are 25/8, 23/12,
22/16, 21/20, 20/32, and 19/88. This component also retains the 24/12 parent
and a second 23/12 coordinate choice. See `PROOF.md` for the universal proof
and inherited boundary, and `section.tex` for the report-ready exposition.

Every JSON packet lists all quantified integer variables, six authentic
fixed coefficient ports, and all residuals. Its equation is the sum of
their squares. High-degree residuals are completely inlined but factored;
the explanatory register dictionaries introduce no additional unknowns.

## Offline checks

From this directory, with Python 3.10 or newer and the sibling `guards`
component present:

    python3 check.py
    python3 -O check.py
    python3 check_projections.py
    python3 -O check_projections.py

All four commands use only the standard library. They check actual fixed
coefficient bindings, exact source and row identities, inverse maps,
declaration closure, and nonzero degree certificates. They do not establish
the inherited unbounded native compiler or Pell theorem by finite tests.

Optional full regeneration requires SymPy for the first command:

    python3 build.py
    python3 build_projections.py

The final source packets are:

- `joint25_octic.json`: 25 variables, 13 rows, degree 8.
- `joint24_degree12.json`: 24 variables, 12 rows, degree 12; projection parent.
- `joint23_degree12.json`: eliminate V; 23 variables, 11 rows, degree 12.
- `joint23_degree12_eliminate_I.json`: eliminate I using the row identity;
  23 variables, 11 rows, degree 12. This has the smaller expanded support.
- `joint22_degree16.json`: 22 variables, 10 rows, degree 16.
- `joint21_degree20.json`: 21 variables, 9 rows, degree 20.
- `joint20_degree32.json`: 20 variables, 8 rows, degree 32.
- `joint19_degree88.json`: 19 variables, 7 rows, degree 88.

`build.py` regenerates the first, second, third, and fifth packets and
`BUILD_CHECK.json`. `build_projections.py` regenerates the other four packets,
`COMPACT_BASE24.json`, and `PROJECTION_BUILD.json`. `check.py` writes
`CHECK_normal.json` or `CHECK_optimized.json`; `check_projections.py` writes
the matching `PROJECTION_CHECK_normal.json` or
`PROJECTION_CHECK_optimized.json`. All generated mathematical packet bytes
are deterministic; the check receipts contain no clock-dependent data.

The inspected joint-positivity lemma is attributed to source 68. The
determinant and signed residue orientation remain separately attributed
upstream contributions. The new work is this exact composition and the
degree-sensitive projection family, not a claim of global minimality,
external novelty, or a newly kernel-checked consistency theorem.
