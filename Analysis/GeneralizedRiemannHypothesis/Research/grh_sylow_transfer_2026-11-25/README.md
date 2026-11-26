# Beyond Dirichlet GRH: Sylow-filtered prime races

**Start with `report.pdf`.** The complete LaTeX source is `report.tex`.

The note proves a general reduction from Dedekind RH for an arbitrary finite
Galois extension of Q to a single one-sided smoothed prime sum, using Dirichlet
GRH and Sylow subgroups of the commutator group. A second theorem treats
PSL(2,7), where weights 21 and -1 on split and involution primes suffice.
Neither theorem assumes global Artin holomorphy. The missing ingredient is an
arithmetic estimate analogous to the covolume inequality in the upstream Lean
proof. No new unconditional nonabelian RH or other open conjecture is claimed
solved. Priority is not certified.

## Reproduce the supplied checks

Python 3.10+ (standard library):

    python3 verify_groups.py > regenerated.json
    diff -u group_certificate.json regenerated.json

Optional illustrative prime computations (requires SymPy):

    python3 sample_prime_races.py > samples.csv
    diff -u prime_race_samples.csv samples.csv

The group certificate uses exact integer/rational calculations; the numerical
prime-race samples are floating-point uncentered sums, not asymptotic proofs.
The polynomial Galois-group determination for Trinks' septic is a published
input; the S5 group determination is proved in the manuscript.

Rebuild the PDF (TeX Live with AMS packages, xurl and hyperref):

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

Upstream source audit, if you have separately cloned lsernau/grh-lean:

    python3 audit_source.py /path/to/grh-lean

This checks the selected Git blob IDs recorded from the connector. It does not
compile Lean. We did not execute this offline checkout audit or the upstream
Lean build here. External machine checks are documented in the bibliography.
`prior-reports.md` identifies which earlier archives were sampled.

Verify archive integrity from the extracted directory:

    sha256sum -c SHA256SUMS

No repository modifications were made.
