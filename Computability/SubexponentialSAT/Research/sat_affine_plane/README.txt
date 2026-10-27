FINITE GEOMETRY FOR ADAPTIVE CONTRACTION
Research prepared for Vladimir Reshetnikov, October 26, 2026 (Pacific date)

MAIN RESULT
Under the inherited normalized Boolean tensor-contraction interface:
  time  = poly(s + description_length) * 2^((30.69133782428595... + o(1)) s/sqrt(log2(s)))
  space = poly(s + description_length) * 2^((29.46603025659479... + o(1)) s/sqrt(log2(s)))
Safe eventual coefficients are 30.692 and 29.467.
Newest reviewed comparable cached coefficients: 30.891018920366... time,
30.753912832055... space. The improvements are about 0.6464% and 4.1877%
in the leading upper-bound coefficients. They are not measured speedups.

The new geometric idea uses the four parallel-line partitions of F_3^2.
Its complete-operation support coefficient is exactly 1/sqrt(3), with a
short geometric proof and independent exact checks. A second four-plan
certificate on 13 groups improves the paid recursive bottleneck.

LIMITS
This uses subexponential cached space. It does not improve the current
polynomial-space coefficient 46.184845586731... or the SAT logarithmic order
n log log n / sqrt(log n). The conditional n/log n-type routes remain
unproved. Constants are per normalized Boolean wire, not per SAT variable.
No end-to-end SAT solver, implemented fast matrix backend, or new Lean
formalization is supplied. The mathematical result imports the existing
exact tensor interface and a known rational fast matrix multiplication theorem.

REVIEW
ProveIt pin: 73dfb5e5ab6e91bd7375e5b97ef85d7e1cc8e81d
20 filed packets and all 9 incoming ZIPs were reviewed.
Closing head: 7de9d09fecd17de776d712835ecb2011205c531d.
The nine ZIPs were then filed by a7ae5ab55f9627f5af7bf77443b3c34ef8ef1be4.
All 443 placed files match the reviewed archive members; no mathematical
change. Current docs/incoming contains only its README. The included closing
map records current paths for all 29 filed packets.
Additional user-supplied source:
anthropics/formal-math@1a6eee293b9e00cb432eef6018a21f523623a9af
The linked source now publicly contains the Lean proof and successful
published build/Comparator/nanoda evidence on an identical Git tree.
We retrieved this evidence; we did not rebuild that large development locally.

FILES
report.tex and sections/ : complete manuscript source
report.pdf              : compiled manuscript
code/certify.py          : primary exact support and schedule checker
code/portfolios.json     : all fixed 9- and 13-group plans
code/verify_affine9.py   : independent affine-plane reconstruction
code/verify_portfolio13.py : independent 13-group reconstruction
code/verify_rejected_routes.py : scoped odd-prime and separator identities
code/check_integration.py : third independent Gram/recurrence audit
code/affine_kernel.py    : exact finite nine-factor contraction and selector
code/verify_kernel.py    : seeded exact kernel and negative-control checks
code/reproduce.py       : one-command verification
code/make_figure.py     : optional vector-figure regeneration (matplotlib)
results/               : generated exact receipts and numerical intervals
provenance/            : source pins, incoming hashes, and evidence notes
CLAIMS.json            : imported/new/checked/unresolved claim ledger
MANIFEST.sha256.json   : archive file-integrity ledger (excluding itself)

REPRODUCTION
From this directory:
  python3 code/reproduce.py --optimized
  make pdf

The mathematical checks require only Python's standard library and no
network access. --optimized reruns each checker with python -O and compares
its output. The finite certificates are checked both exhaustively and via
Gram upper bounds with matching witnesses. Exact rational interval
arithmetic certifies the constants; floating-point values are not used to
accept the new inequalities.

The local kernel uses ordinary scalar arithmetic over Z/(2^p), rather than
the asymptotic matrix backend. Its fixtures compare all four plans and the
adaptive selector with brute-force contraction. This verifies the finite
regrouping and selection, not the entire upstream SAT theorem.

INTEGRATION
Suggested destination: a new subdirectory of
Computability/SubexponentialSAT/Research/.
Record both time and space coefficients and preserve the stronger resource-
restricted branches. Preserve the corrected public-formalization link.
The archive does not modify or push anything to the repository.

Read the report's final section for further research questions. The most
important remaining task is a closed implicit contraction representation
that avoids full boundary tables while preserving degree, precision,
construction cost, and efficient recursive entry evaluation.
