Beyond Dirichlet GRH
Coefficient fields of CM newforms and one-sided prime estimates
Research note dated 25 November 2026

Start with report.pdf. Sections 5 and 6 prove the main classification and
list the quintic fields. Section 9 develops a nonabelian test case for
the analytic method. Links in the PDF point to papers and pinned Lean files.

Main results and scope

* Weight-two CM newforms of all levels and all characters yield exactly
  26 quintic coefficient fields, up to isomorphism. For prime degree ell
  at least seven, the fields are in bijection with imaginary quadratic
  fields of class number ell. The proofs in the note use algebraic
  number theory and unconditional class-number results.
* Dirichlet GRH supplies the hypothesis of the published Grosswald
  primitive-root bounds and several cyclic norm-Euclidean classifications.
* For Q(cube_root(2)), the report proves the equivalence between RH for its
  Dedekind zeta function and a particular upper bound on a weighted sum
  over primes. Establishing that upper bound remains an open step.

Contents

report.tex is the entry point for all nine included TeX sections.
report.pdf is the compiled 14-page paper, with clickable source references.
checks/quintic_polynomials.csv contains every polynomial in descending
  coefficient order x5 through x0, including the real cyclotomic case.
  The cm_discriminant column is the imaginary quadratic base discriminant.
checks/quintic_fields.csv contains the norm parameters for the 25
  class-number-five rows. The remaining field is Q(zeta_11 + zeta_11^-1).
checks/quintic_irreducible.csv contains one prime of irreducible reduction
  per field. checks/quintic_witnesses.csv gives one distinguishing prime
  and the two factor-degree patterns for each of the 325 unordered pairs.
checks/ contains the Python programs and their reference outputs.
SHA256SUMS lists the SHA-256 digest of every other archive member.

Reproduce the paper

From this directory, with a standard TeX Live distribution, run

    latexmk -pdf report.tex

Alternatively, run pdflatex report.tex twice to resolve cross-references.

Reproduce the computations

Use Python 3.10 or later. Only the independent polynomial verifier needs an
external Python package (tested with SymPy 1.14.0). From this directory:

    python3 checks/quintic_fields.py > regenerated_quintics.csv
    diff -u checks/quintic_fields.csv regenerated_quintics.csv
    python3 checks/verify_quintics_sympy.py
    python3 checks/primitive_roots.py
    python3 checks/weighted_race.py

The first program also regenerates quintic_witnesses.csv and
quintic_irreducible.csv alongside the program. The SymPy verifier checks
all 26 polynomials, all 25 norm identities, all 26 irreducibility witnesses,
and every pairwise distinction. The race script gives a finite numerical
illustration. The asymptotic statement is proved in the paper.

To check the archive itself from this directory:

    sha256sum -c SHA256SUMS

Lean source and verification

    git clone https://github.com/lsernau/grh-lean.git
    git -C grh-lean checkout 72fead102f663d5c7a407964a13dc0cf9d977207
    python3 checks/source_audit.py grh-lean

The included audit checks the source revision, dependency and toolchain
pins, theorem names, statement identity, and key file digests. Independent
kernel replays and challenge comparisons for this revision are recorded at
https://math.mit.edu/~drew/shortgrh/ . The authors of the present analysis
used that verification record. The deductions in the report are written
mathematical arguments, and have not been independently refereed or
formalized in Lean. The archive excludes the upstream repository and build
dependencies. The pinned links in the report locate them.
