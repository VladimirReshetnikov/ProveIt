BEYOND DIRICHLET GRH
Transferable methods, established consequences, and a concrete Hecke target
Prepared for Vladimir Reshetnikov -- 25 November 2026

Repository examined:
  https://github.com/lsernau/grh-lean
Pinned commit:
  72fead102f663d5c7a407964a13dc0cf9d977207

START HERE

Read report/grh_transfer_analysis.pdf. Its editable, self-contained LaTeX
source is report/grh_transfer_analysis.tex. The report distinguishes the
repository's five exported RH/Dirichlet-GRH statements, consequences obtained
using existing mathematical implications, reusable internal methods, and
proposed extensions whose main arithmetic estimates remain unproved.

The clearest named consequence discussed is Vinogradov's conjecture on the
least quadratic nonresidue, via the existing theorem of Lamzouri, Li and
Soundararajan. This is an established implication of Dirichlet GRH, not a
claim that this analysis discovered a new analytic argument.

The recommended first target beyond Dirichlet GRH is the order-three
ideal-class Hecke character of Q(sqrt(-23)). Its L-function is the
degree-two factor in the Dedekind zeta function of Q(alpha), where
alpha^3-alpha-1=0. The report proves an explicit reduction to a one-sided
principal-ideal prime-sum bound. It does not prove that new arithmetic bound
or announce a proof of Hecke GRH.

CONTENTS

  report/
    grh_transfer_analysis.pdf  Readable mathematical report.
    grh_transfer_analysis.tex  LaTeX source, including references.

  lean/
    Transfer.lean             Seven supplemental elementary transfer lemmas.
    lakefile.toml            Standalone project configuration.
    lean-toolchain           Lean 4.35.0 pin.
    lake-manifest.json       Exact dependency revisions.

  scripts/
    arithmetic_checks.py     Exact arithmetic for the discriminant -23 target.
    nonresidue_checks.py     Exact finite check for primes 5 <= p < 3000.
    static_audit.py          Source-token/import audit of a separate checkout.
    reproduce_checks.sh     Runs the two Python arithmetic checks; optionally
                            also runs the static audit on a pinned checkout.

  data/
    arithmetic_checks.json  Reduced forms, S3 characters, local factors,
                            theta coefficients, and principal-class selector.
    nonresidue_checks.json  Results for 428 primes in the indicated range.
    static_audit.json       Recorded static audit of the pinned upstream source.

  evidence/
    arithmetic_checks.log  Output of the exact arithmetic checker.
    lean_transfer_check.log
                           Output of checking the packaged Transfer.lean,
                           including the axioms printed for all seven lemmas.
    provenance.json       Snapshot, hashes, pins and verification scope.
    source_audit.txt       Detailed source and endpoint inspection.
    mathlib_endpoint_audit.txt
                          Pinned Mathlib semantics and transfer review.
    upstream_source_72fead1.tar.gz
                          Complete, unchanged git-archive source snapshot.
    pdf_quality_check.json
                          PDF rendering and layout verification record.

  licenses/
    Upstream Apache-2.0 license, attribution, and notice records.

The complete upstream source is included as a compressed tar archive with its
original licenses and notices. Its uncompressed SHA-256 agrees with the
independent verification record. Downloaded toolchains, dependency caches,
and .lake directories are excluded; the dependency versions are pinned.
SHA256SUMS records the integrity hashes of all other files in this package.

REPRODUCE THE FINITE CHECKS

Requirements: Python 3.9 or later; standard library only. These commands do
not download software and do not install or build the full GRH development.
Run from the top-level directory of this extracted archive:

  bash scripts/reproduce_checks.sh

The script explicitly writes:

  data/arithmetic_checks.json
  data/nonresidue_checks.json
  evidence/arithmetic_checks.log

Equivalent individual commands, again from the archive's top-level directory:

  python3 scripts/arithmetic_checks.py --output data/arithmetic_checks.json
  python3 scripts/nonresidue_checks.py > data/nonresidue_checks.json

Use ordinary Python, not python -O, for nonresidue_checks.py: its mathematical
checks are expressed as assertions. arithmetic_checks.py uses explicit checks
that remain active under optimization. All comparisons use exact integers or
fractions; floating-point decisions are not used.

The arithmetic checker exhaustively enumerates reduced positive binary forms
of discriminant -23 using 3*a^2 <= 23. It checks the cubic discriminant and
factorization modulo 23; S3 character decompositions and local Euler-factor
polynomial identities; 24 prime/theta-coefficient comparisons through 97; and
the local principal-ideal selector. The theta comparison is finite consistency
evidence, not a proof of an identity at every prime.

The nonresidue checker finds the least quadratic nonresidue at each prime
5 <= p < 3000 using Euler's criterion. Rational lower bounds for log(p),
obtained from a positive atanh series after binary scaling, establish the
strict inequality n(p) < (log p)^2 for that finite range. The infinite result
requires the cited analytic theorem together with Dirichlet GRH.

REPRODUCE THE STATIC SOURCE AUDIT

For a Git checkout with commit metadata, obtain the repository and select
the exact snapshot:

  git clone https://github.com/lsernau/grh-lean.git grh-lean
  git -C grh-lean checkout 72fead102f663d5c7a407964a13dc0cf9d977207

From the archive's top-level directory, substitute the actual absolute path:

  python3 scripts/static_audit.py /absolute/path/to/grh-lean > data/static_audit.json

For an offline source audit, first extract evidence/upstream_source_72fead1.tar.gz
into a new empty directory and pass that directory directly to static_audit.py.
The extracted archive has no .git directory, so the scanner reports a null commit
and Git may emit a diagnostic; file hashes still allow exact comparison with
the recorded audit. Its original commit is recorded in provenance.json.

Alternatively, run both finite checks and the static audit of a Git checkout:

  bash scripts/reproduce_checks.sh /absolute/path/to/grh-lean

The optional script route checks the checkout's HEAD against the pinned hash
before running the audit. The audit removes nested comments and strings before
screening selected Lean tokens, records file hashes and import reachability,
and compares the two editions' exported statement files. It is deliberately
not a Lean parser, elaborator, proof checker, or proof-kernel replay. Absence
of a suspicious token does not itself establish a theorem's truth.

REPRODUCE THE STANDALONE LEAN CHECK

This small project uses:

  Lean/Lake: leanprover/lean4:v4.35.0
  Mathlib:   56a005855ea17e0b0958f73ec801ae140b0a1679

The manifest pins Mathlib's transitive dependencies. Keep these revisions when
reproducing the recorded result. Use a matching Lean/Lake installation in PATH,
or an elan setup that honors lean/lean-toolchain. Fetching dependencies and
precompiled caches requires network access and is separate from the Python
checks above. From the archive's top-level directory:

  cd lean
  lake exe cache get Mathlib.Tactic.Linarith Mathlib.Tactic.Ring Mathlib.Analysis.SpecialFunctions.Pow.Real
  lake env lean Transfer.lean > ../evidence/lean_transfer_check.log 2>&1

A zero exit status means Lean accepted the seven supplemental lemmas. Their
printed dependencies in the recorded log are propext, Classical.choice, and
Quot.sound. The packaged project configuration and unchanged theorem source
were checked together. Dependency caches are intentionally excluded.

The supplemental lemmas concern an abstract determinant comparison, its sharp
index-corrected form, error exponents, and transfer through a finite product.
Their substantial arithmetic and analytic inputs are explicit hypotheses.
They do not construct theta lifts, prove an L-function factorization, prove the
cubic prime-sum estimate, or independently prove RH or GRH.

REBUILD THE PDF

A conventional TeX Live installation with the packages named in the source
is sufficient. The bibliography is included in the source; no external .bib
file or downloaded figure is required. From the archive's top-level directory:

  cd report
  pdflatex -interaction=nonstopmode -halt-on-error grh_transfer_analysis.tex
  pdflatex -interaction=nonstopmode -halt-on-error grh_transfer_analysis.tex

The second pass resolves references and the table of contents. The included
PDF is the reviewed output; a rebuild can differ bytewise because of TeX
versions and PDF metadata while preserving mathematical content.

VERIFICATION LIMITS

The full upstream GRH proof was NOT independently rebuilt or replayed in this
analysis. The report identifies published verification records and separates
those external checks from the source inspection, Python calculations, and
small standalone Lean check actually performed for this package.

Likewise, no claim is made to have read and understood every line of the large
development. Selected mathematical interfaces and final statements were read,
and a static scan covered the snapshot. The archive's small Lean lemmas do
not certify the upstream repository by implication.

THE PRECISE REMAINING CUBIC ESTIMATE

Let K=Q(sqrt(-23)), let H be its Hilbert class field, and let gamma_H denote
the constant term divided by the residue in the Laurent expansion of zeta_H
at s=1. For a nonzero ideal a of K, Lambda_K(a)=log(Np) when a is a power
of a prime ideal p, and is zero otherwise. Let 1_[a]=1 select principal
ideal classes. Define

  R(X) = sum_(Na <= X) Lambda_K(a) * 1_[a]=1 * (1/Na - 1/X)
           - log(X)/3 + (1+gamma_H)/3.

The proposed next arithmetic theorem is: for every epsilon>0, there are
C_epsilon and X_epsilon such that

  R(X) <= C_epsilon * X^(-1/2+epsilon)  for all X >= X_epsilon.

The report proves that this bound would imply RH for zeta_H and the desired
order-three Hecke L-function. It remains an unproved target in this package.
The practical obstacle is that the new ideal-class information lives at split
rational primes, while the existing geometric prime detector is tailored to
its auxiliary quadratic splitting and cyclotomic residue-class data.

STATUS AND ATTRIBUTION

The source snapshot and external verification status are dated explicitly in
the report. Established results retain their original attribution. Newly
written reductions and checks are not represented as novel resolutions of
open conjectures. Upstream notices are preserved in licenses/.
