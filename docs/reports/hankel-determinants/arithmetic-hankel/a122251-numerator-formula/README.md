# A Proof of an OEIS Hankel-Numerator Conjecture

**Research article and reproducible exact-arithmetic implementation**  
Prepared 19 September 2026 by GPT-6 Astra Pro.

## Result

For positive integers a,m with gcd(a,m)=1 and n >= 0, put

    H_n(m,a) = det(1/(a+m(i+j)))_{0<=i,j<=n}.

The matrix size is **n+1**. Its reduced numerator is

    A_n(m,a) = product_{p|m} p^(n(n+1)*v_p(m) + 2*sum_{k=0}^n v_p(k!)).

In particular it is independent of the coprime offset a, is a square, and
contains no prime factors outside those dividing m. Taking m=p prime and a=1
proves the formula recorded as a conjecture in OEIS A122251, including the
p=2 instance in A122249.

The article also proves exact denominator valuations and

    gcd_{a>=1, gcd(a,m)=1} denominator(H_n(m,a))
      = the part coprime to m of product_{k=0}^n (2k+1)*binomial(2k,k)^2.

It supplies a constructive congruence witness for each primewise minimum,
an independent inverse-matrix explanation, the noncoprime-parameter formula,
recurrences, digit-sum asymptotics, and a natural-boundary proof for the
prime-exponent generating function. The denominator gcd is not asserted to
be attained as one individual denominator.

## Read

- `report.pdf`: compiled article (19 pages, including title and contents).
- `report.tex`: complete, self-contained LaTeX source; bibliography is embedded.
- `research_status.md`: scope of the result, attribution, and priority caveat.
- `oeis_update_draft.txt`: proposed proof comment; **not submitted** to OEIS.
- `sources.json`: the consulted source records and access date.

The main elementary proofs are in Sections 1–4. No software is needed to
follow them. The plane-partition interpretation uses the classical MacMahon
formula and is not needed to prove the main numerator or denominator theorem.

## Run the calculations

Python **3.10 or newer** is required. No third-party packages, network access,
or symbolic-algebra system are needed. The included run used Python 3.13.5.

From the extracted directory:

```sh
python code/verify.py
python code/hankel_arithmetic.py 3 3 1 --matrix-check
python code/hankel_arithmetic.py 2 4 2 --matrix-check
```

The first command reruns all checks and regenerates the CSV and text files in
`data/`. To preserve the included observation log, use another output folder:

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

The full run passes **123,298 checks**, including **2,304 independently
eliminated matrices** (each compared both with the product and the numerator
formula). See `data/verification.json` for category counts. These are finite
checks, not substitutes for mathematical proofs or proof-assistant validation.

## Code entry points

`code/hankel_arithmetic.py` can also be imported. Useful functions are:

- `determinant(hankel_matrix(n,m,a))`: independent exact elimination.
- `determinant_product(n,m,a)`: Cauchy product as a `Fraction`.
- `numerator_factorization(n,m,a)`: proved reduced-numerator factorization.
- `predicted_numerator(n,m,a)`: the expanded integer numerator.
- `denominator_valuation(n,m,a,q)`: exact local formula for coprime a,m.
- `universal_denominator(n,m)`: denominator gcd over coprime offsets.
- `sharpness_witness(n,m,q)`: an offset attaining the minimum q-valuation.
- `inverse_formula(n,m,a)`: explicit four-binomial inverse matrix.
- `prime_exponent_sequence(n,p)`: E_p(n), where A_n(p)=p^(2 E_p(n)).

Factoring uses trial division and is intended for moderate parameter values.
The factored formula can be evaluated far beyond the practical range of
matrix elimination, but printing very large expanded integers is constrained
by output size and Python's integer-string conversion limits. Arithmetic-step
bounds in the article are not claims about bit complexity or fast factoring.

## Data

`numerators.csv` contains exact reduced fractions and numerator factorizations
for n=0,...,12, a=1, and m in {2,3,4,5,6,7,10,12} (104 rows).

`exponents.csv` gives E_2,E_3,E_5,E_7 for n=0,...,512 (513 rows).

`gcd_witnesses.csv` contains 457 explicit primewise sharpness witnesses used
in the 84 finite gcd certificates.

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

No external bibliography program, image files, downloaded sources, or custom
font files are required. Standard font packages must be installed through
the user's TeX distribution; font files are not distributed in this archive.

## Research status

The OEIS entries consulted on 19 September 2026 still mark the relevant
formulas as conjectural. This article supplies complete proofs of those
formulas and the stated extensions. It does **not** certify that no prior
proof or more general classical result already implies them. The Cauchy
determinant, Cauchy inverse, MacMahon enumeration, and the p=3 exponent
generating function are explicitly treated as existing results.

No peer review, formal proof-assistant verification, external submission,
or persistent repository modification was performed. Only original research
artifacts and independently computed data are included; third-party paper
PDFs are not redistributed.
