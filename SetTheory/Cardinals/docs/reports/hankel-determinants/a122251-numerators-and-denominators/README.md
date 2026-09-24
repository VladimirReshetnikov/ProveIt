# A Proof of an OEIS Hankel-Numerator Conjecture

**Research article and reproducible exact-arithmetic implementation**  
Prepared 19 September 2026 by GPT-6 Astra Pro, with AI-assisted research notes
merged in (see *Provenance* below).

## Result

For positive integers a,m with gcd(a,m)=1 and n >= 0, put

    H_n(m,a) = det(1/(a+m(i+j)))_{0<=i,j<=n}.

The matrix size is **n+1**. Its reduced numerator is

    A_n(m,a) = product_{p|m} p^(n(n+1)*v_p(m) + 2*sum_{k=0}^n v_p(k!)).

In particular it is independent of the coprime offset a, is a square, and
contains no prime factors outside those dividing m. Taking m=p prime and a=1
proves the formula recorded as a conjecture in OEIS A122251, including the
p=2 instance in A122249.

The article also proves the closed form

    A_n(m,a) = m^(n(n+1)) * [P_n]_m^2,
    B_n(m,a) = Q_n(m,a) / ((P_n)_{perp m})^2,   P_n = product_{k<=n} k!,

where [u]_m is the part of u supported on the primes of m and u_{perp m} is
its complementary part; the integrality of the denominator is proved, not
assumed. It proves exact denominator valuations and

    gcd_{a>=1, gcd(a,m)=1} denominator(H_n(m,a))
      = the part coprime to m of L_n = product_{k=0}^n (2k+1)*binomial(2k,k)^2

(the determinant of the inverse Hilbert matrix, OEIS A005249), and shows that
this gcd is already the gcd of the denominators at only **two** explicitly
constructed offsets.

It supplies a constructive congruence witness for each primewise minimum, an
independent inverse-matrix explanation derived in two ways, the noncoprime
numerator *and* denominator formula, an extension to unequal row and column
steps, recurrences, digit-sum asymptotics, and a natural-boundary proof for
the prime-exponent generating function. The denominator gcd is realized as
the gcd of two constructed denominators; it is **not** asserted to be attained
as one individual denominator.

For unequal steps, the article proves that the reduced numerator of

    det(1/(a + m1*i + m2*j))_{0<=i,j<=n}

has no prime factor outside those of m1*m2 and that its reduced denominator is
divisible by the part of L_n coprime to m1*m2. No shift-independent numerator
formula is claimed there.

## Provenance

This report is a merge of two independently produced research reports on the
same OEIS conjecture:

- `a122251-numerator-formula` (the base document: structure, notation, macros);
- `a122251-prime-exclusion-proof` (indexed by matrix size m = n+1).

Both proved the shared core theorem by the same argument — Cauchy's double
alternant, an exact residue-square count, Legendre's factorial valuation, and
the same Chinese-remainder sharpness construction — so that argument appears
exactly once here, in the base document's words and indexing. Where the two
genuinely differed, both proofs are kept and marked as such: the explicit
inverse matrix is derived by rational interpolation and again by a cofactor
computation from Cauchy's identity, and the Lambert-series generating function
is derived from second differences and again from first differences. Every
ported statement, example, table row and test range was reindexed from matrix
size m to the OEIS index n = m-1.

## Read

- `report.pdf`: compiled article (28 pages, including title and contents).
- `report.tex`: complete, self-contained LaTeX source; bibliography is embedded.
- `research_status.md`: scope of the result, attribution, and priority caveat.
- `oeis_update_draft.txt`: proposed proof comment; **not submitted** to OEIS.
- `sources.json`: the consulted source records, revision tags, and access date.

The main elementary proofs are in Sections 1–4. No software is needed to
follow them. The plane-partition interpretation uses the classical MacMahon
formula and is not needed to prove the main numerator or denominator theorem.

## Run the calculations

Python **3.10 or newer** is required. No third-party packages, network access,
or symbolic-algebra system are needed. The included run used Python 3.14.4.

From the extracted directory:

```sh
python code/verify.py
python code/hankel_arithmetic.py 3 3 1 --matrix-check
python code/hankel_arithmetic.py 2 4 2 --matrix-check
```

The first command reruns all checks and regenerates the CSV, JSON and text
files in `data/`. To preserve the included observation log, use another output
folder:

```sh
python code/verify.py --output /tmp/hankel-verification
```

The `(n,m,a)=(3,3,1)` example prints:

```text
H_3(3,1) = 4782969/36653693440000
numerator factorization: {3: 14}
denominator: 36653693440000
Independent exact matrix check: PASS
```

All tested arithmetic is exact. The direct matrix routine uses rational
Gaussian elimination, independently of the Cauchy product. The numerator
routine includes the scaling correction for noncoprime parameters.

The full run passes **159,555 checks**, including **4,505 independently
eliminated matrices** (2,304 Hankel matrices compared both with the product
and with the numerator formula, 2,187 unequal-step matrices, and 14 published
OEIS terms), plus 168 further eliminations while writing the sample table.
See `data/verification.json` for category counts. These counts come from one
single run of the merged suite; they are not the sum of the totals advertised
by the two merged reports, whose ranges overlap and whose indexings differ.
These are finite checks, not substitutes for mathematical proofs or
proof-assistant validation.

## Code entry points

`code/hankel_arithmetic.py` can also be imported. Useful functions are:

- `determinant(hankel_matrix(n,m,a))`: independent exact elimination.
- `determinant_product(n,m,a)`: Cauchy product as a `Fraction`.
- `numerator_factorization(n,m,a)`: proved reduced-numerator factorization.
- `predicted_numerator(n,m,a)`: the expanded integer numerator.
- `denominator_valuation(n,m,a,q)`: exact local formula for coprime a,m.
- `universal_denominator(n,m)`: denominator gcd over coprime offsets.
- `sharpness_witness(n,m,q)`: an offset attaining the minimum q-valuation.
- `two_shift_certificate(n,m)`: the constructed two-offset gcd certificate.
- `inverse_formula(n,m,a)`: explicit four-binomial inverse matrix.
- `biarithmetic_matrix(n,m1,m2,a)`, `biarithmetic_product(n,m1,m2,a)`: the
  unequal-step determinant, entrywise and by the Cauchy evaluation.
- `prime_exponent_sequence(n,p)`: E_p(n), where A_n(p)=p^(2 E_p(n)).

Every function uses the same convention: `n` is the OEIS index and the matrix
has size n+1. Factoring uses trial division and is intended for moderate
parameter values; the certificate routine finds the primes of a huge
denominator by factoring only the 2n+1 small entry denominators, and no
determinant numerator or denominator is ever factored. The factored formula
can be evaluated far beyond the practical range of matrix elimination, but
printing very large expanded integers is constrained by output size and
Python's integer-string conversion limits. Arithmetic-step bounds in the
article are not claims about bit complexity or fast factoring.

## Data

`numerators.csv` contains exact reduced fractions and numerator factorizations
for n=0,...,12, a=1, and m in {2,3,4,5,6,7,10,12} (104 rows).

`oeis_numerators.csv` contains formula-generated reduced numerators for
n=0,...,35 (matrix size recorded explicitly), a=1, and m in {2,3,4,5,6,10,12}
(252 rows).

`small_determinants.csv` contains 168 directly eliminated exact determinants
for n=0,...,5, m in {1,2,3,4,6,10,12} and a in {1,2,3,5}, including noncoprime
pairs.

`exponents.csv` gives E_2,E_3,E_5,E_7 for n=0,...,512 (513 rows).

`gcd_witnesses.csv` contains 457 explicit primewise sharpness witnesses used
in the 84 finite gcd certificates.

`gcd_certificates.json` contains 20 constructed two-offset certificates
(n, m, a1=1, a2, both denominators, their gcd, and the predicted gcd); the
large denominators are stored as decimal strings for portability.

`A122249_terms.txt` and `A122251_terms.txt` contain independently computed
terms for n=0,...,30. They are not downloaded OEIS b-files or accepted edits.

`verification.json` and `verification.txt` retain the exact check totals and
one observed elapsed time. Rerunning changes the time, not the expected totals.

## Rebuild the PDF

A TeX installation with `latexmk`, pdfLaTeX, NewTX, AMS packages, `microtype`,
`tcolorbox`, `listings`, `fancyhdr`, and `hyperref` is sufficient:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

Without `latexmk`, the included `build.sh` runs two `pdflatex` passes, keeps
intermediates in `.build/`, tails the log on failure, and copies the result to
`report.pdf`:

```sh
sh build.sh
```

No external bibliography program, image files, downloaded sources, or custom
font files are required. Standard font packages must be installed through
the user's TeX distribution; font files are not distributed in this archive.

## File inventory

```
README.md              this file
report.tex             article source
report.pdf             compiled article (28 pages)
build.sh               two-pass pdflatex build script
research_status.md     status, attribution, claim boundaries
sources.json           consulted records with revision tags
oeis_update_draft.txt  proposed OEIS comment (not submitted)
code/hankel_arithmetic.py   exact arithmetic library
code/verify.py              regression and theorem audit
data/numerators.csv         104 rows, n<=12
data/oeis_numerators.csv    252 rows, n<=35
data/small_determinants.csv 168 directly eliminated determinants
data/exponents.csv          513 rows of E_p(n)
data/gcd_witnesses.csv      457 primewise witnesses
data/gcd_certificates.json  20 two-offset certificates
data/A122249_terms.txt      independently computed terms
data/A122251_terms.txt      independently computed terms
data/verification.json      category counts and totals
data/verification.txt       same totals, plain text
```

## Research status

The OEIS entries consulted on 19 September 2026 still mark the relevant
formulas as conjectural; the retrieved internal revision tags were
`#2 Mar 30 2012 18:59:15` for A122251 and `#6 Oct 27 2024 12:12:17` for
A122249. The same retrieval is dated 18 September 2026 in America/Los_Angeles;
the encyclopedia's page footers use Eastern time and are the site-wide update
stamp, not an entry's revision date. This article supplies complete proofs of
those formulas and the stated extensions. It does **not** certify that no prior
proof or more general classical result already implies them. The Cauchy
determinant, Cauchy inverse, MacMahon enumeration, the inverse Hilbert
determinant A005249, and the p=2 and p=3 exponent generating functions
(A122247, A122250) are explicitly treated as existing results.

No peer review, formal proof-assistant verification, external submission,
or persistent repository modification was performed. Only original research
artifacts and independently computed data are included; third-party paper
PDFs are not redistributed.
