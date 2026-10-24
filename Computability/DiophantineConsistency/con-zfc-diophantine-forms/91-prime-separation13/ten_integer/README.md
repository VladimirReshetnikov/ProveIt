# Three fewer operations for four ten-integer equations

This component replaces three arithmetic subexpressions in four existing
ProveIt equations. Each delivered circuit computes **exactly the same
integer polynomial** as its indicated parent. The domain remains ten
unrestricted integers, and all actual fixed coefficient values are
unchanged.

| Delivered graph | Parent operations | Operations here | Exact total degree |
|---|---:|---:|---:|
| `integer10_predecessor.json` | 480 | **477** | 1,245,324 |
| `integer10_linear.json` | 484 | **481** | 1,179,788 |
| `integer10_cubic.json` | 487 | **484** | 1,114,252 |
| `integer10_sixterm.json` | 521 | **518** | 1,081,125 |

One operation means one live binary addition, subtraction, or multiplication.
Reusing an existing node and reading an integer leaf cost zero under this
convention. There are three fewer multiplication nodes; the norm rewrite
also exchanges one addition for one subtraction. Coefficient sizes, exact
degrees, and zero sets are preserved. This is an ancillary circuit
simplification; it makes no optimality or historical-priority claim.

## The three identities

All symbols below abbreviate existing polynomial subexpressions. They add
no quantified variables.

1. Share the already needed cube when forming the fifth power:

   \[
   S^3=S S^2,\qquad S^5=S^2S^3.
   \]

   The former separate chain through \(S^4\) becomes unnecessary.

2. Rewrite the two-root norm, with the parent circuit's norm inputs
   \(Z,\Sigma,a_0,a_1\):

   \[
   \begin{aligned}
   &(Z^2-\Sigma^2(a_0+a_1))^2-4\Sigma^4a_0a_1\\
   &\quad=(Z^2+\Sigma^2(a_0-a_1))^2
            -4Z^2\Sigma^2a_0.
   \end{aligned}
   \]

3. Factor the discriminant expression to reuse the existing \(4g\):

   \[
   \begin{aligned}
   &8g\,\mathrm{cap}^3K^2
    -g^2\bigl(32(C-KL)^2\mathrm{cap}^3+g^2K^2\bigr)\\
   &\quad=8g\,\mathrm{cap}^3
       \bigl(K^2-4g(C-KL)^2\bigr)-g^4K^2.
   \end{aligned}
   \]

These identities hold in every commutative ring. Substitution into the
parent polynomials proves equality for all integer inputs and transfers
their exact degrees and consistency equivalence. No search for solutions
is involved.

## Contents and source attribution

- `upstream/` is a byte-for-byte copy of the complete `norm10/` component
  from the supplied `con_zfc_polynomial_shears` package, including all
  coefficient payloads, source data, proofs, notices, licenses, and degree
  certificates. Its predecessor is `upstream/upstream/integer10.json`.
- `provenance/report.pdf` is the unchanged parent report. Its TeX and
  section inputs are retained alongside it. Sections 2--4 give the parent
  shear and exact-degree arguments. Parent provenance, attribution, and
  calibration notes are included. The original upstream README's relative
  link to `../report.pdf` should be read here as `provenance/report.pdf`.
- `SOURCE_PINS.json` gives byte sizes and SHA-256 hashes of every copied
  source file, plus the incoming archive digest. Older repository snapshot
  pins remain in the copied provenance files.
- `CHECKS_*.json` and `SUMMARY.json` contain reproducible receipts for the
  four optimized graphs.
- `VERIFICATION_NORMAL.json`, `VERIFICATION_OPTIMIZED.json`, and
  `VERIFICATION_RUNS.json` record matching normal/`-O` results, including
  a check that verification from an unrelated directory modifies no files.

The graph field `fixed_coefficients` points to
`upstream/FIXED_COEFFICIENTS.json`. Payload paths inside that manifest are
relative to the manifest's directory. The twelve fixed integer leaves are
actual supplied integers, not extra existential parameters.

For the three sheared variants, `degree_upper_bound` remains 1,245,324: it
is the naive syntactic DAG bound. The smaller proved total degree is the
separate `exact_degree` field. The verifier checks the source's cancellation
certificates and nonzero leading coefficients over the actual fixed data.

## Reproduce and verify

Python 3 and its standard library suffice. From this directory:

```sh
python3 optimize_shears.py
python3 verify.py
python3 -O verify.py
```

The first command regenerates the four graphs and their receipts. Both
verification commands are read-only; no delivered receipt is overwritten.
`python3 optimize_shears.py --check` is another read-only entry point.
All required conditions use explicit exceptions, so `-O` retains the checks.

An archive-level verifier can call the same function without changing its
working directory or import path:

```python
import runpy
entry = runpy.run_path('/absolute/path/to/ten_integer/verify.py')
result = entry['verify_all']()  # JSON-serializable dictionary; no writes.
```

The verifier checks source hashes, coefficient recipes and payloads, graph
topology and live counts, deterministic reconstruction, exact sparse local
ring identities, and the unchanged circuit contexts. Context equality uses
exact interned terms, with associative/commutative multiplication; it does
not rely on random evaluations or hash equality. This also verifies the
shared-power replacement in the actual parent graphs.
Two negative controls preserve graph validity and operation counts but
reverse the final subtraction or permute two prefix variables; the exact
checker rejects both.

Separately, it runs 1,024 reproducible modular evaluations per variant,
assigning arbitrary residues to every fixed leaf and variable. Those are
**finite transcription diagnostics**, not a proof of a universal identity
or of consistency equivalence. The exact algebra establishes the new local
polynomial equalities. The unbounded native/compiler/refutation calibration
is inherited from the supplied ProveIt sources and is not re-proved by these
computations. No new end-to-end proof-assistant certificate is asserted.
