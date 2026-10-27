ASYMMETRIC PACKET BALANCING FOR SUBEXPONENTIAL SAT
Research memorandum for Vladimir Reshetnikov -- October 26, 2026

START HERE
Read report.pdf. The complete editable LaTeX is report.tex, which includes
annulus_modes.tex. The bibliography and source_manifest.json identify all
reviewed commits, seven proposal archives, and the exact preprint sources.

MAIN RESULT
Under the exact contraction framework of the cited OpenAI preprint, for a
root network with at most s Boolean wires and maximum degree ceil(s^0.9),

  time <= poly(s + description length)
          * 2^((76.90899495160009... + o(1)) s / sqrt(log2(s))),
  space = polynomial.

The coefficient has the exact expression

  pi * sqrt(5/2) * (9 + sqrt(3)) / ln(2).

The new ingredients are deterministic asymmetric pair-load balancing,
near-unit packet padding, use of the fresh side's smaller recursive degree,
and a schedule that adds only a logarithmic precision buffer. These combine
with the earlier sharp Hermite precision and factorial Cauchy modes.
The earlier best explicit normalized certificate among the seven packets
was 648.4410666487529. Composing that schedule with its separate factorial
mode improvement gives 374.3776243832656. These are upper-bound coefficient
comparisons, not ratios of actual SAT runtimes.

A separate new annulus Cauchy basis exploits the actual reciprocal row
domain. It preserves source-family counts and strengthens weights term by
term. Its fixed-level slopes are 4, 16/5, 64/21, 256/85, ...; they tend to 3,
so it does not raise the uniform global slope above 3.

The low-degree specialization (maximum degree <= ceil(s^(1/12))) has
coefficient 31.06413206299. It has stronger input assumptions and includes
bounded-degree clause networks for sufficiently large sizes.

WHAT IS AND IS NOT ESTABLISHED
The new lemmas have ordinary mathematical proofs, independently reviewed
within this research effort, and exact finite checks of their components.
The unchanged upstream deformation, recovery, and child-factorization
framework is an explicit dependency. We did not run a Lean/Rocq build or
verify the full upstream formalization. The code is not an end-to-end SAT
solver, and its finite checks are not SAT performance benchmarks.

The general SAT logarithmic order is unchanged:

  poly_k(n,m) * 2^O_k(n loglog(n) / sqrt(log(n))).

The strongest prior density-sensitive envelope remains available. The new
numeric coefficients are per normalized Boolean wire, not per SAT variable.
A numerical variable-level coefficient needs the encoding's wire constant.
The conditional n/log(n)-type targets in prior packets are not established
algorithms, and this archive does not close their missing interfaces.

FILES
report.pdf / report.tex / annulus_modes.tex
  Full review, theorems, proofs, dependency boundary, comparisons, and
  further research questions.
code/balanced_packing.py
  Exact rational pair-load balancing and uniform orientation packets;
  multiedges and asymmetric degree bounds supported.
code/verify_packing.py
  Independent exhaustive expectation checks, packet invariants, asymmetric
  fixtures, and invalid/corrupted-input controls.
code/annulus_modes.py
  Importable orderings, rational source/target features, exact tuple counts,
  and finite rational / unramified-extension verification.
code/verify_schedule.py
  Exact parameter margins, schedule identities, and numerical constants.
run_checks.py
  Reruns all new component checks, normally and under Python optimization.
results/
  Recorded deterministic component outputs and combined verification.
source_manifest.json / sources/upstream/
  Immutable source URLs, commit IDs, Git blob hashes, and SHA-256 hashes.
  The four reviewed upstream TeX files are included byte-for-byte, with
  the upstream license and preprint README; their directory is flattened.
INTEGRATION.txt / PROOF_STATUS.json
  Exact replacement points and claim-by-claim proof/dependency status.
build_report.py / Makefile
  PDF rebuild, without network access or shell escape.
verify_bundle.py / SHA256SUMS
  Check packaged file bytes before rerunning generators or changing files.
qa/pdf_review.json
  Final compilation, page-count, and visual-review record.

REPRODUCE
Python 3.10 or newer, standard library only, for the mathematical checks:

  python3 run_checks.py

Or run one component:

  python3 code/verify_packing.py
  python3 code/annulus_modes.py
  python3 code/verify_schedule.py

The scripts write results under results/. All mathematical verification
gates remain active under python -O. Some comparisons use floating point
only to display constants; exact margins and identities use integers or
fractions.Fraction. The full asymptotic proof is in the report, not inferred
from finite samples.

For PDF creation, install pdfLaTeX with the standard packages used by the
preamble (AMS, Latin Modern, geometry, microtype, booktabs, longtable,
enumitem, xcolor, xurl, hyperref, fancyhdr):

  python3 build_report.py

The script uses three passes and disables shell escape. No bibliography
processor, external image, network download, or upstream script is needed.
The build directory is disposable; report.pdf is copied from a successful
build. PDF bytes may differ across TeX versions even when content is equal.

To verify original packaged bytes, before running generators:

  python3 verify_bundle.py

Checksums establish internal consistency of this delivery, not a digital
signature. Newly generated results can differ if the code is modified.

SOURCE SNAPSHOTS
OpenAI: 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a
ProveIt placement: 2b925d8800cda68f5723b65dc1fcdaf3d8170359
The earlier incoming snapshot was aa6933442eb936962de79ba6d321cd0391c450bd.
The seven reviewed archives were placed unchanged under
Computability/SubexponentialSAT/Research during the review.
No GitHub branch, file, issue, or pull request was changed by this delivery.
