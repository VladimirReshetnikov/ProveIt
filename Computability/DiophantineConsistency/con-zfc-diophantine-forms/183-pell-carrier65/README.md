# A first Pell root eliminates an index quotient

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026, with AI assistance.

## Result

The complete primary equation has **14 strictly positive integer variables,
65 binary integer arithmetic operations, and exact degree 150**. It improves
the matched admissible942 parent at repository commit
02a78a08603cbae248c19c23a75907c6c6bd6443, which has 15 variables, 66 operations,
and degree 157. All four fixed integer coefficients are unchanged.

An ordinary mathematical argument, composed with the pinned
P66/native/K215/refutation calibration, establishes in ZFC that the equation
has no positive integer zero if and only if Con(ZFC). No assumption of
consistency or inconsistency is used to prove the equivalence.

Start with **report.pdf** for the proof and complete specification.
**equation.pdf** is a standalone one-page specification. Both editable
LaTeX sources are included.

| Equation file | Independent domain | Variables | Binary operations | Exact degree |
|---|---|---:|---:|---:|
| equation/carrier65.json | Strictly positive integers | **14** | **65** | **150** |
| equation/natural14.json | Nonnegative integers | 14 | 79 | 150 |
| equation/integer42.json | Unrestricted integers | 42 | 163 | 300 |

Every JSON gives a literal integer-only arithmetic program and a fixed
coefficient binding. The primary split is 37 multiplications, 16 additions,
and 12 subtractions. All declared inputs, coefficient ports, and gates are live.
The operation metric counts fixed-integer leaves and reused registers at zero
cost. It is not a bit-complexity measure.

## The new idea

Remove the old positive variables h,tau, introduce n>0, and set

~~~
tau = E*n+k-R.
~~~

Delete Nk=k-h*E-R from the product. The new equation is

~~~
N0*N1*Na*Nt*Ns-Delta = 0.
~~~

The first Pell norm already forces tau=1 (mod E). After noncircular sign
and rank recovery, this restores the omitted positive quotient
h=(k-R-1)/E. Canonical parent zeros give
n=(tau-k+R)/E>0. The complete proof is in report.tex/pdf and
proofs/CARRIER65_PROOF.md.

The second result stores transition targets as reverse-discovery distances.
The new mixed-radix decoder uses 399 base62 numeral characters instead of 436,
while reconstructing exactly the same 430 actions, 942 indexed tiles and all
four fixed integers. The one-page source includes every numeral character and
all decoding overhead. The complete coefficient recipe shrinks from 1992
to 1980 nonwhite pdftotext -raw characters. Whole-page TeX bytes fall 5025
to 5014; word count and rebuilt PDF bytes increase. These metrics are separate.

## Files

- report.tex, report.pdf: full article, new proofs, coefficient recipe,
  domain translations, all 65 arithmetic rows, and the one-page specification.
- equation.tex, equation.pdf: complete standalone one-page equation.
- equation/: all three literal programs, the 399-character numeral, four
  minimal unsigned big-endian coefficient files, and coefficient hashes.
- code/: constructor, exact polynomial checks, independent arithmetic and
  decoder checkers, and pure coefficient reconstruction functions.
- evaluate.py: evaluation of an explicitly supplied tuple.
- verify.py: read-only finite release verification.
- proofs/: detailed new arguments and independent internal AI reviews.
- sources/: byte-exact immediate parent files, source pins, the retained
  ordinary calibration proofs, and the unchanged finite certificate.
- licenses/: inherited licenses and machine attribution.
- verification/: actual normal/optimized receipts and page metrics.

K0 in the arithmetic JSON is the printed constant K; MF is the printed
source mask and the binary file MF_source.bin. The register scaled_Ns is
exactly the displayed factor Ns.

## Verify and reconstruct

Python 3.10 or later and its standard library suffice. No network or proof
assistant is required for the finite checks.

~~~bash
python3 -B verify.py
python3 -B -O verify.py
python3 -B code/build.py
~~~

The last command reconstructs eight equation/coefficient files and requires
byte identity. To write a reconstruction into a new directory:

~~~bash
python3 -B code/build.py --output-dir /tmp/conzfc-carrier-rebuilt
~~~

The verifier compares all 430 actions and 942 tiles, all four full integer
values, the coefficient scalar boxes, every arithmetic gate, all formula
boundaries, exact total degree, source identities, and deliberate corruption
controls. The separate arithmetic checker does not import producer code.
The separate seed checker uses successive divmod, rather than prefix-floor
digit extraction.

The checks do not search for zeros, decide consistency, or replace the
unbounded mathematical proofs.

## Evaluate a supplied tuple

Use a JSON array in the exact order of the selected program's witnesses:

~~~bash
python3 -B evaluate.py tuple.json
python3 -B evaluate.py --domain natural tuple.json
python3 -B evaluate.py --domain integer tuple.json
~~~

The default output gives the exact zero test, sign, magnitude bit length,
and magnitude hash. The --value option also prints the entire decimal value,
which can be large. Booleans, nonintegers, wrong coordinate counts, and values
outside the declared domain are rejected.

## Build the PDFs

Use make pdf, or:

~~~bash
pdflatex -interaction=nonstopmode -halt-on-error equation.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
~~~

Standard TeX Live packages suffice. The report includes the compiled
one-page equation at its end. Its own source also prints the full formula
and constant recipe. Rebuilding PDFs can change font or metadata bytes;
after an intentional rebuild use verify.py --skip-manifest. The exact
arithmetic and coefficient comparisons remain active.

## Scope and attribution

The new reduction is a strict improvement of the specified parent, not
a proof of global minimality. Smaller-variable representations in other
degree/cost regimes already exist. The final primary construction retains
the K215/native route, despite investigating alternatives. The repository's
related mixed-radix and quotient-carrier work is explicitly credited.

The equivalence is an ordinary proof formalizable in ZFC, with the identified
inherited calibration. This archive does not contain a complete compilable
Lean/Rocq dependency closure or a newly checked end-to-end formal proof.
Canonical parent completeness is sufficient; the optional stronger
all-zero bijection invokes the additional inherited sign-recovery theorem.
Internal AI-assisted reviews are not external human endorsements.

See INTEGRATION.md for additive placement and SHA256SUMS for file identities.
