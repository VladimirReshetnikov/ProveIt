# One quadratic constraint for many Pell certificates

Research contribution prepared for Vladimir Reshetnikov, 24 October 2026.

The principal deliverable is a completely explicit quartic polynomial in
**378 unrestricted integer variables**. Its lack of integer solutions is
equivalent in ZFC to Con(ZFC), by the new ordinary arithmetic arguments
composed with the retained ProveIt numerical-calculus/refutation calibration.
A complementary quartic uses **242 nonnegative integer variables**.

The main new theorem combines a size bound, simultaneous Pell-index
identification, and both coordinate signs in the single quadratic relation

    V = W + sum_i ((X_i - 1)^2 + (Y_i - e_i)^2) + (A - 1) Q,   Q >= 0.

One complete indexed-Pell anchor at W is retained, including its private
domain conditions. The theorem and its constructive converse are proved
in the paper; the exact hypotheses are part of the theorem. The route uses
the direct C222 numerical calculus and does not instantiate K215 or Jones.

## Completed equations

| Endpoint | Domain | Variables | Quadratic residuals | Degree | Collected monomials | Coefficient height |
|---|---|---:|---:|---:|---:|---:|
| Principal | All integers | 378 | 230 | 4 | 9,421 | 3,054,220 |
| Companion | Nonnegative integers | 242 | 190 | 4 | 9,308 | 18,049,118 |

Each equation is **the sum of the squares of every listed residual, equal
to zero**. The coordinate order, all residuals, and all collected quartic
coefficients are supplied. There are no unexpanded arithmetic predicates,
variable-length lists, enormous hidden fixed parameters, or unevaluated
machine encodings in the final coefficient files.

The natural equation improves the inspected 261-natural construction in
variables, residuals, support and height. The integer equation saves 64
variables and 60 residuals against the inspected 442-integer construction;
its support and height increase. Smaller-variable high-degree equations
remain a different tradeoff. No global minimum or literature-wide priority
claim is made.

## Read first

- `report/report.pdf`: complete paper, ordinary proofs, comparison, and all
  230 literal integer residuals.
- `report/report.tex` and the other `.tex` files: complete editable source.
- `portable/CLAIMS.json`: exact endpoint paths, metrics, and SHA-256 hashes.
- `portable/integer378/equation.json` and `expanded_polynomial.json`:
  principal integer equation and every expanded coefficient.
- `portable/natural242/natural/`: corresponding natural equation.
- `portable/*/residuals.txt` (or the natural subdirectory): readable equations;
  `variables.tsv` maps zero-based coordinate numbers to source names.
- `portable/SIGNED_CONSTRUCTION_PROOF.md` and `GUARD_TABLE.tsv`: complete
  ordered sign proof and all 36 scalar plus 12 product predicates.
- `portable/audits/MATH_REVIEW.md`: independent mathematical review.
- `portable/SOURCE_LEDGER.json`: source snapshot, exact input-archive hashes,
  and the 76 retained source-file hashes.
- `diagnostics/`: small exact Pell examples, signed cases and the explicit
  counterexample to dropping Q's nonnegativity.

`z0`, `z1`, ... in the text files denote the indexed variables in the JSON.
The paper calls the natural coordinates `u_0`, `u_1`, ... only to distinguish
the two domains. Every variable in the integer endpoint ranges independently
over all of Z; every variable in the natural endpoint ranges over {0,1,2,...}.

## Reproduce and verify offline

Python 3.10 or later, standard library only. From this directory:

```bash
python3 -B verify_document.py
python3 -B diagnostics/check_one_row_cap.py
cd portable
python3 -B verify_release.py --rebuild
python3 -B -O verify_release.py --rebuild
python3 -B audits/audit_interfaces.py natural242
python3 -B audits/audit_signed.py
```

The two rebuild commands use fresh temporary output directories and compare
all 27 generated normative JSON files byte for byte. Both normal and optimized
Python runs passed. Optimized mode is propagated to construction subprocesses.
The checker replays all 117 natural and 125 integer inverse substitutions,
every translated row, all 250 literal sign identities, the exact guard layout,
and every final collected coefficient. Three intentionally corrupted algebraic
certificates are rejected. The separate interface audits check the full raw
frame, anchor, aggregate cap, all six exact-power ports, eleven modular ports,
and the noncircular sign-recovery order.

`verify_document.py` independently parses every displayed integer residual
back from TeX, checks both plain-text equation lists, and verifies the report's
metrics and hashes against the delivered coefficient files. These are exact
finite checks. The unbounded semantic argument is the ordinary proof in the
paper and retained source texts, not finite enumeration of possible zeros.

To rebuild the PDF, from the bundle root:

```bash
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

PDF bytes may vary with the TeX distribution and build metadata; the equation
hashes and exact JSON reconstruction do not. The delivered PDF was rendered
and visually checked, and its build had no overfull boxes or unresolved
references.

## Mathematical and formalization boundary

The equivalence proved is

    ZFC proves: (there exists z in Z^378 with P(z)=0)
                  iff (there exists a finite ZFC refutation).

Negating gives the requested equivalence with Con(ZFC). This is not a claim
that ZFC proves either consistency or the polynomial's unsolvability.

The retained logical interfaces are `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The new arithmetic
reductions have ordinary unbounded proofs formalizable in ZFC. This archive
does not claim a newly compiled end-to-end Lean/Rocq proof term for the final
coefficient file or an encoded object-language ZFC derivation. The inherited
calibration is identified and retained rather than silently re-proved by an
algebraic checker.

The square frame and signed-power-output corollary in the paper are optional
generalizations. The measured 378-integer endpoint uses the doubled linear
frame with its atom signs established first. Four independently retained
power-output guards are essential to its acyclic sign proof.

## Provenance and integration

Inspected repository snapshot:
`f4d8db99e060339f3306a04d507c35bc1d0d68c5`.

The three direct incoming dependencies are pinned in the source ledger:

1. `ConZFC_Shared_Binomial_Certificates_2026-10-24.zip`.
2. `ConZFC_Shared_Pell_Bound_261_2026-10-24.zip`.
3. `ConZFC_Unified_Binomial_Even_Indices_Round15_2026-10-24.zip`.

Their required Python modules, ordinary proofs, endpoint snapshots, licenses
and notices are included. No checkout or network access is needed to rebuild
the coefficients. `baselines/` retains the exact small metric excerpts used
in the comparison and their archive-member provenance.

This folder can be placed in `docs/incoming/` as a research packet or its
equations and proofs can be moved into the appropriate research directory.
No repository branch, commit, pull request or publication is created by this
delivery. Preserve the inherited license and notice files when integrating.
`SHA256SUMS` binds every delivered file except itself.
