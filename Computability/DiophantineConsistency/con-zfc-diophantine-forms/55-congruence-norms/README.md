# Congruence separation and positive-word fusion

**A research package for ProveIt, 23 October 2026.**

The principal result is an explicit polynomial in **ten unrestricted integer
variables**, of **exact total degree 9,152,284**, with **586 live binary arithmetic
operations**. Its integer solvability is equivalent to existence of a zero of
the retained fixed positive source. Composing with the inherited source compiler
and K215 calibration gives the ordinary mathematical theorem formalizable in ZFC:

> The equation has no integer solutions if and only if ZFC is consistent.

This proves the equivalence, not the consistency or unsolvability statement.
The fixed integers are fully specified; no coefficient is selected by assuming
consistency, and no halting search is used to generate them.

## Results and comparisons

Baseline: ProveIt commit `4b4349064a750ba6347293b55874a7f92abdd0db`, including
all eight incoming archives available there. See `BASELINE.json` and the
independent intake review in `audits/FRONTIER_AUDIT.md`.

| Construction | Supplied domain | Exact degree | Live operations | Primary circuit |
|---|---|---:|---:|---|
| New two-root integer form | 10 integers | 9,152,284 | 586 | `ten/generated/signed10_b2.json` |
| Incoming selective baseline | 10 integers | 21,111,400 | 659 | Baseline archive |
| New majorant form | 9 positive integers | 5,671,669 | 630 | `nine_majorant/generated/calibrated_positive.json` |
| New cheaper form | 9 positive integers | 6,692,108 | 604 | `nine_fast/generated/calibrated_positive.json` |
| Incoming selective baseline | 9 positive integers | 7,344,328 | 738 | Baseline archive |
| New auxiliary-gap form | 14 positive integers | 52 | 79 | `fourteen/polynomial.json` |
| Incoming support-sensitive baseline | 14 positive integers | 56 | 79 | Baseline archive |

The nine-variable natural-coordinate circuits have the same respective degrees
and cost 636 and 610 operations. These are different domains from unrestricted
integers. Operations count live binary `add`, `sub`, and `mul` nodes, including
squaring and multiplication by a numeral; fixed coefficient leaves cost zero.
They are circuit costs, not bit costs or optimal-circuit lower bounds.

The ten-integer result improves the strongest incoming degree by **56.65%** and
its circuit size by **11.08%**. The nine-positive majorant improves the strongest
incoming degree by **22.77%** and its circuit size by **14.63%**. Neither result
reduces the number of variables. Existing lower-operation, higher-degree points
remain relevant; for example the incoming nine-positive 548-operation form and
ten-integer 582-operation form remain separate tradeoffs. No global minimum or
exhaustive literature-priority claim is made.

## What changed

1. **A combined square and positivity guard.** In the integer construction,
   `r=bQ` has coprime factors, both congruent to 1 modulo 3. Requiring
   `a=r+(3*Delta-1)*(r*z)^2` to be a square with `z != 0` recovers both positive
   square factors and `Delta > 0`. Constructive Pell witnesses prove the converse.
2. **Congruence separation.** The ten-variable radicands satisfy `a/b` odd and
   `d/b` even on every signed assignment. The nine-variable radicands are 1 and
   0 modulo 4. A quartic two-root norm therefore replaces expensive separating
   weights, and in the ten-variable case replaces the larger eight-factor norm.
3. **Preserved constructive witnesses.** The new restrictions on packed and
   Lucas coordinates are justified from the actual constructive Lucas indices.
   Arbitrary solutions are not assumed to occur in desired residue classes.
4. **A global positive-word substitution.** Keeping the original positive
   quadratic residuals and evaluating the word `1+g+ell` reduces 136 weighted
   source records to 94. Two target positions are repaired and the complete
   49,632-interaction isolation certificate is supplied.
5. **A second cancellation for the nine-variable majorant.** Removing the old
   separation padding exposes a lower-degree defect expansion. The degree is
   proved by an exact polynomial identity and a nonzero leading coefficient.
6. **A smaller secondary construction.** The fourteen-variable form combines a
   positive auxiliary gap with the stronger canonical congruence modulo `f^2`.

## Read first

- `report.pdf` — typeset mathematical report, complete new equations and proofs,
  explicit source and coefficient recipes, complexity comparisons, and limitations.
- `report.tex`, `metrics.tex` — complete editable LaTeX source.
- `INTEGRATION.md` — proposed repository integration and formal proof obligations.
- `native/SOURCE_CHAIN.md` — exact inherited compiler/calibration dependency chain.
- The `PROOF.md` in each arithmetic component — additional local detail.

## Reproduce the finite checks

Python 3.10 or newer, standard library only:

```bash
python3 verify.py
```

This checks the manifest, recreates the generated arithmetic circuits in a
temporary copy, requires byte-identical circuit outputs, and runs the independent
source, coefficient, degree, congruence, norm, and gap checks. It performs no
network access and does not run an unbounded Turing-machine simulation. A
machine-readable result is written to `REPRODUCTION.json`.

Individual components can be rebuilt directly:

```bash
python3 ten/build.py
python3 ten/verify.py
python3 nine_majorant/build_nine.py
python3 nine_majorant/check_ring_identities.py
python3 nine_majorant/check_circuits.py
python3 nine_fast/build_nine.py
python3 nine_fast/verify_source.py
python3 nine_fast/check_circuits.py
python3 fourteen/build.py
python3 fourteen/verify.py
```

The exact native coefficient regeneration command and optional inherited Lean
endpoint build are documented inside `native/`. A Lean kernel rebuild was not
performed during this session. The new literal end-to-end reductions have no
new Lean or Rocq proof artifact.

To rebuild the report using an ordinary TeX Live installation:

```bash
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

## Certificate versus primary equation

The nine-majorant `_certificate.json` files compute **`D^16 * F9`**. Their exact
degree is 7,900,853, whereas the primary polynomial has degree 5,671,669. The
multiplier and both leading coefficients are explicitly identified in the degree
records. These certificate circuits are checking artifacts, not the recommended
630-operation evaluator. The nine-fast certificate is a different expression
for the same polynomial, with multiplier one.

## Fixed coefficients and explicitness

All arithmetic branches use the whole package-31 tuple
`wang943-mixed-121x8801`, with `MF_source` already shifted. The four port bit
lengths are 1,064,921; 1,070,004; 1,064,921; and 1,064,922. They are fixed
integer leaves, not extra unknowns. The compressed payloads, byte hashes,
finite tile compiler, and 430 literal machine actions are included. The source
records and powers of two then specify every derived fixed coefficient.
The source scale and nine-variable threshold are large fixed powers of two;
this release does not claim a coefficient-height improvement.

Copied `SOURCE_PINS.json` and historical binding files retain their original
provenance. Some historical proof-path strings describe their original package
layout; the live files and current component proofs are identified above and in
the top-level dependency ledger. The verifier binds the actual payload bytes.

## Proof status

The new arithmetic reductions are proved in ordinary mathematics in the report.
The finite checks verify implementations and finite identities; bounded tests do
not prove the unbounded semantic equivalence. The native-window compiler, K215
calibration, Jones ratio theorem, and (for the ten-integer branch) Sun's 2026
modified Lucas interpolation theorem are explicitly inherited inputs. The
ten-integer branch therefore retains that preprint dependency; the nine-positive
branch does not use it.

The pinned repository's separate external Lean theorem for a generic closed
nine-variable coefficient recipe must not be described as formal verification
of these newly emitted circuits. An exported object-language ZFC derivation is
also distinct and is not supplied here. The archive includes same-session
independent AI-assisted reviews, not external human peer review.

No remote repository files were changed or published. New material is supplied
under the accompanying MIT No Attribution license for incorporation in ProveIt; all retained
third-party notices and licenses continue to apply.
