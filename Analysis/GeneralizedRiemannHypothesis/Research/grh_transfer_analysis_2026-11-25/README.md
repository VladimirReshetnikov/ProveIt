# Beyond Dirichlet GRH: source audit and transfer analysis

Prepared for Vladimir Reshetnikov, November 25, 2026 (Pacific date).

This archive analyzes [lsernau/grh-lean](https://github.com/lsernau/grh-lean), identifies mathematical results that can use its exported RH/Dirichlet-GRH theorems, and develops concrete research directions beyond those endpoints. Start with **`report.pdf`**; **`report.tex`** is its complete editable LaTeX source.

## Main findings and status

- **The public statements have the intended scope.** The inspected endpoint uses Mathlib's Riemann zeta function and Dirichlet L-functions for every positive modulus. This is Dirichlet GRH, not a theorem about all Artin or automorphic L-functions.
- **There are immediate mathematical transfers.** Existing RH/GRH-conditional theorems give, for example, the value zero of the de Bruijn–Newman constant and published norm-Euclidean classifications in cyclic degrees five and seven. These are applications of established implications, not priority claims for new proofs of those implications.
- **The proof contains reusable mechanisms.** The report explains the comparison of short forms with twisted determinant lower bounds, a one-sided transform criterion, and a weakening of the auxiliary-prime requirement to a sufficiently populous subfamily. The paper-level reductions are proved in the report; no novelty or Lean-verification claim is made for them.
- **The next nonabelian target is explicit.** For the degree-two Artin L-function associated with `X^3-X-1`, the report gives positivity calculations and a conditional zero-exclusion reduction. The required arithmetic estimate and auxiliary-twist selection remain unproved.
- **Some tempting transfers have concrete obstructions.** The report identifies missing ramification and witness-quantifier hypotheses relevant to proposed Vandiver and integral K-theory arguments. It does not claim a new proof of those conjectures or of BSD.

### What was actually verified here

We inspected the pinned source, executed the bundled static audit, reproduced exact finite arithmetic certificates, checked symbolic residue identities, and compiled the LaTeX report to PDF. The static inventory finds 803 readable-edition modules and 794 compact-edition modules, all locally reachable from `Main`; it finds no admitted-proof or extra-axiom tokens in either `src` tree under the documented lexical scan.

**We did not run the full Lean build, replay the repository through a kernel, or run an independent proof checker locally.** Compilation and independent-checker results discussed in the report are explicitly attributed to the repository maintainers and the external verification projects cited there. A lexical scan is not an axiom-dependency check. Successful Python calculations and PDF compilation do not verify the Lean development.

The additional file **`lean/TransferExamples.lean` is an uncompiled source template**. It supplies wrappers for real-zero exclusion, finite Dirichlet-L products, and transfer along a separately supplied factorization. It contains no admitted proofs, but its compilation has not been established in this analysis. In particular, it does not supply a formal Dedekind-zeta factorization.

## Exact source version

| Component | Pinned version |
|---|---|
| Repository | `https://github.com/lsernau/grh-lean` |
| Audited commit | [`72fead102f663d5c7a407964a13dc0cf9d977207`](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207) |
| Lean toolchain | `leanprover/lean4:v4.35.0` |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` |

The audit records the working-tree state, source hashes, manifest pins, comparator configuration, and local import graph. Its dependency scan stops at external imports; it does not scan or verify the pinned Mathlib dependency tree.

## Archive contents

| File or directory | Purpose |
|---|---|
| `report.pdf` | Complete research report, including proofs, transfer assessment, limitations, and bibliography. |
| `report.tex` | Complete LaTeX source for the PDF. |
| `code/build_pdf.sh` | Portable three-pass pdfLaTeX build; produces `report.pdf`. |
| `code/static_audit.py` | Read-only source inventory, lexical absence scan, SHA-256 hashes, pins, and local import reachability. |
| `code/finite_certificates.py` | Exact bounded reduced-form enumeration, S3 character calculations, and a witness-quantifier counterexample. |
| `code/analytic_checks.py` | SymPy checks of transform residues, cancellation, and the covolume comparison identity. |
| `data/static_audit.json` | Full recorded static-audit output for the pinned checkout. |
| `data/finite_checks.json` | Summary of the executed finite arithmetic checks. |
| `data/idoneal_certificates.json` | All accepted reduced forms and an explicit rejection witness for every rejected integer through the stated bound. |
| `data/idoneal_numbers.csv` | The accepted integers through 10,000, order discriminants, and class numbers. |
| `data/analytic_checks.json` | Recorded symbolic-check output. |
| `lean/TransferExamples.lean` | Uncompiled downstream theorem wrappers, importing upstream `Main`. |
| `README.md` | This guide and reproduction instructions. |
| `data/provenance.json` | Bibliographic URLs, evidence status, runtime versions, executed-check record, and PDF quality assurance. |
| `SHA256SUMS` | SHA-256 hashes for every other delivered file. |

The 65 idoneal integers found through 10,000 agree with Euler's list in that range. **The finite enumeration does not prove that no further idoneal integer exists above 10,000.** The connection with ideal classes uses the classical reduction theory stated in the report. The S3 calculations and symbolic examples likewise establish their specified finite or algebraic assertions, not the missing analytic estimates for the proposed Artin-GRH target.

## Reproduce the Python checks

Run the commands below from the directory containing this README. Python 3.11 or later is sufficient for all scripts. The finite and static checks use only the standard library; the static audit also invokes `git`. The analytic checks require **SymPy** in the chosen Python environment.

To keep the delivered evidence intact, the examples write fresh outputs under `build/reproduced-data`:

```bash
mkdir -p build/reproduced-data
python3 code/finite_certificates.py --limit 10000 --out build/reproduced-data
python3 code/analytic_checks.py > build/reproduced-data/analytic_checks.json
```

The finite script accepts `--limit` from 1 through 10,000 and defaults to 10,000. It creates `finite_checks.json`, `idoneal_certificates.json`, and `idoneal_numbers.csv` in the `--out` directory. The analytic script takes no command-line options and prints JSON to standard output. If SymPy is not installed, install it in your preferred Python environment, for example with `python3 -m pip install sympy`.

### Reproduce the source audit

A separate checkout of the upstream repository is needed. Use a fresh destination, or substitute the path to an existing checkout at the exact audited revision:

```bash
git clone https://github.com/lsernau/grh-lean.git ../grh-lean-audit
git -C ../grh-lean-audit checkout --detach 72fead102f663d5c7a407964a13dc0cf9d977207
python3 code/static_audit.py ../grh-lean-audit \
  --output build/reproduced-data/static_audit.json
```

The script reports whether the checkout matches the reference commit and whether the working tree is clean. It inventories the actual working files, so local edits can change its results even when `HEAD` is correct. Module reachability is file-level reachability, not declaration-level proof dependency. Deliberate `Challenge.lean` admissions used by upstream Comparator are reported separately from the main source trees.

## Rebuild the PDF

A normal TeX Live or MiKTeX installation with pdfLaTeX is sufficient. The document uses Latin Modern, AMS packages, `mathtools`, `geometry`, `microtype`, `booktabs`, `longtable`, `tabularx`, `array`, `enumitem`, `xcolor`, `hyperref`, `fancyhdr`, TikZ/PGF, and `listings`. The bibliography is contained in the LaTeX source; no BibTeX or Biber step is required.

```bash
sh code/build_pdf.sh
```

The script locates the project relative to its own location, runs pdfLaTeX three times with shell escape disabled, and copies the completed PDF to `report.pdf`. Auxiliary files and per-pass logs are written under `build/pdf`. If a pass fails, its log is printed and the script exits with a nonzero status. It requires an already functioning local TeX installation and performs no network downloads or system configuration changes.

## Optional: build upstream Lean and then check the wrappers

These instructions describe a future reproducibility check; they are **not a record of a build performed for this archive**. Install a Lean toolchain manager such as `elan`, retain the upstream toolchain and Mathlib pins, and allow the resources stated in the upstream README. The repository estimates one to two hours on 12 cores with 24 GB RAM for its build, with additional time if the Mathlib cache is unavailable; independent checking has separate requirements.

After creating the pinned sibling checkout in the source-audit example, run this from the report directory:

```bash
grh_report_dir=$(pwd)
(
  cd ../grh-lean-audit/grh
  lake exe cache get
  lake build
  lake env lean scripts/PrintAxioms.lean
  lake env lean "$grh_report_dir/lean/TransferExamples.lean"
)
```

The last command deliberately runs only after the source build. It checks the wrapper file using the upstream project's environment without copying it into the audited checkout. Inspect the actual command results and printed axiom dependencies before describing the wrappers as compiled or verified. A successful Lean build alone should not be conflated with an independent-checker run; follow the upstream instructions for those additional checks.

## Interpretation and attribution

Consequences that use the repository's RH/GRH endpoint inherit the correctness and intended interpretation of that endpoint. The report distinguishes those consequences from the paper-level arguments proved here, finite checks, uncompiled formal templates, and research obligations that remain unsolved. Primary citations and source-level theorem locations are given in the report. The labels `New` and `Lib` in upstream paths are organizational labels, not certificates of mathematical novelty.
