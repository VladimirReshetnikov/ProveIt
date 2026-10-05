# Reproducibility and verification for Report181

## Requirements, scope, and trust boundary

Python 3.10 or later and its standard library suffice for the exact verifier,
certificate regeneration, corruption guards, manifest checks, and packaging
logic. The PDF build additionally requires an installed TeX distribution with
`pdflatex`, `kpsewhich`, and the manuscript's packages. `pdftex` is needed if a
private local format must be initialized. The builder does not download or
install software, invokes no shell, and passes `-no-shell-escape` to TeX.

The exact core imports neither SymPy nor mpmath. Arithmetic uses arbitrary-
precision Python integers and `fractions.Fraction`. Optional mpmath scout
programs and their old numerical output are segregated under `optional/` and
`data/references/`. They are not executed by the builder. Reading their hashes
does not independently certify their floating-point results.

The finite computations below establish the identities actually tested. They
do not prove analytic zero-freeness, full-circle decay, uniform differentiated
remainders, asymptotic error estimates, inverse estimates, conditional limit
laws, joint independence, or global novelty. The conventional proofs and their
hypotheses appear in `Report181.tex`. This is not a proof-assistant certificate.
In particular, the formal H-series is never treated as a convergent series at a
positive argument, and no numerical saddle computation enters the exact core.

## Run the exact core

From the package root:

```
python -I -S -B code/verify.py
python -I -S -B -O code/verify.py
python -I -S -B guard_tests.py
python -I -S -B -O guard_tests.py
python -I -S -B test_build.py
python -I -S -B -O test_build.py
```

`-I` isolates Python from user environment and user-site settings; `-S` disables
site-package loading; `-B` prevents bytecode cache writes. `-O` demonstrates that
validation does not rely on removable assertions. All core validation uses
explicit exceptions. The exact verifier's normal and optimized JSON results
must be identical. Runtime timings and machine-specific paths are excluded.

## Exact results and independent algorithms

1. **All coefficients through 600.** Ordinary truncated integer polynomial
   convolution computes

   F(q) = product over k >= 1 of (1 + q^k P_k(q)),
   P_k(q) = product over 1 <= j <= k of (1-q^j)^(-1).

   At step k, the standard partition recurrence computes P_k; a separate new
   array computes multiplication by 1+q^k P_k. Factors with k>600 cannot affect
   this truncation. There is no digit packing, approximate arithmetic, or call
   to the scout's coefficient routine. Every one of the 601 integers is
   compared with the frozen file whose SHA-256 is
   `2149f443f6524faec57311834867a404eae8a612b8fef70f5df6b59faa35c0ad`.
   The complete generated array is also stored in `data/certificates.json`.

2. **Independent composition enumeration through 18.** A direct recursive
   generator counts compositions whose maximal weakly decreasing runs have
   strictly increasing first parts. The recursion either continues a decreasing
   run or starts a new run at a value greater than its previous leader. It does
   not consult partition counts or the product. The values for n=0,...,18 are

   1, 1, 2, 4, 8, 15, 28, 51, 92, 164, 289, 504, 871, 1493, 2539,
   4290, 7201, 12017, 19939.

   These equal both the convolution prefix and the literal marked prefix in the
   manuscript. Finite strict increase from a_1 to a_600 and a_n<=2^(n-1) for
   1<=n<=600 are checked, without presenting finite checks as an infinite proof.

3. **Formal finite-end coefficients through degree 10.** Rational truncated
   power-series arithmetic evaluates the finite coefficient problem

   H(z) = sum over k>=1 of log(1 + exp(k z) product_{j=1}^k(1-exp(-j z))).

   To obtain degree d, only k<=d occurs, since the k-th summand has valuation k.
   All exponential and logarithmic operations are formal and truncated. The
   exact h_1,...,h_10 are

   1, 2, 7, 68/3, 391/4, 40043/90, 96787/40, 17366357/1260,
   157752233/1728, 285439229213/453600.

   Overlapping degree-8 and degree-10 truncations are also checked for agreement.

4. **Edgeworth tuple generator.** For h=1,2 the code enumerates every tuple of
   nonnegative integers m_j, 3<=j<=2h+2, with sum (j-2)m_j=2h. If J=sum j m_j,
   its exact term is

   (-1)^(J/2) (J-1)!! b^(-J/2) product_j kappa_j^m_j/(m_j! (j!)^m_j).

   Thus

   E1 = kappa_4/(8 b^2) - 5 kappa_3^2/(24 b^3),

   E2 = -kappa_6/(48 b^3) + 7 kappa_3 kappa_5/(48 b^4)
        + 35 kappa_4^2/(384 b^4) - 35 kappa_3^2 kappa_4/(64 b^5)
        + 385 kappa_3^4/(1152 b^6).

   The output records the coefficient, b exponent, cumulant exponents, Gaussian
   degree, and weighted degree of every term. The formal leading substitution
   b=6 A^2/t^5 and kappa_j=(A^2/2)(3)_j/t^(3+j) yields

   E1_leading = -35 t^3/(144 A^2),
   E2_leading = -1295 t^6/(41472 A^4).

   The second line is the leading substitution into E2 alone, not the entire
   order-t^6 coefficient of a fully re-expanded saddle approximation.

5. **Free-energy algebra through positive degree 10.** A small exact sparse
   Laurent-polynomial implementation uses the independent basis (t,A,ell,Z),
   where A=pi^2/6, ell=log(t/(2*pi)), and Z=zeta(3). It expands

   mu^2/(2t) + A/t + mu/2 + t/12 - Z/t^2
     - sum c_(2m) t^(2m) + H(t),
   mu=A/t+ell/2-t/24.

   Bernoulli numbers are generated from their exact rational recurrence;
   zeta(-r)=-B_(r+1)/(r+1) for positive odd r supplies the MacMahon c_(2m).
   The separately tracked terms are -log(t)/12-zeta'(-1). The displayed terms
   through t^3 are independently compared with

   A^2/(2t^3) + (A ell/2-Z)/t^2 + (ell^2/8+35A/24)/t
   + 11 ell/48 + 1225t/1152 + 5761t^2/2880 + 7t^3.

   Adding -log(t)/12 changes the logarithmic coefficient to 7/48 and leaves
   the constant -11 log(2*pi)/48-zeta'(-1), as in the report. Full coefficients
   through t^10 are in the certificate. Formal coefficient agreement is not an
   analytic remainder bound.

6. **Constant-order Legendre identity.** In the exact Laurent basis
   (s,A,D,ell,C), substitution B=D+A/4 and u1=D/(2s^2) checks that

   (-20/s^2)u1^3/6 + (6B-5A/2)u1^2/(2s^4) + (ell/4-C)u1/s^2
   = D^3/(3s^8) - A D^2/(8s^8) + D(ell/4-C)/(2s^4).

   This checks the algebraic cancellation used in the constant-order formula.
   It does not computationally certify its asymptotic remainder.

7. **Frozen input integrity.** Literal SHA-256 pins in `code/verify.py` cover
   the selected frozen source copies, optional scout scripts, independent audit
   result, and `data/PROVENANCE.json`. The upstream `FROZEN.json` lists additional
   upstream documents not distributed here. The core checks only the selected
   included files; it does not pretend to reproduce all upstream hash checks.

## Certificate format and corruption defenses

`data/certificates.json` is canonical sorted, indented JSON ending in a newline.
Its exact independently derived object must serialize identically to the frozen
certificate. This rejects missing or extra keys, altered scope claims, changes
in any stored coefficient or basis, floats or booleans in place of integers,
and noncanonical rational strings such as `2/2`. The JSON reader also rejects
duplicate keys (including nested ones), NaN, Infinity, and trailing data.

`guard_tests.py` deliberately corrupts each category of result, all h_j and
Edgeworth coefficients, all polynomial terms, manuscript data and markers,
frozen-input syntax, and pins. It checks ordinary and optimized subprocesses,
byte-identical regeneration, exclusive output creation, and rejection of
symlinks, symlinked parents, directories, and FIFOs as data. It also exercises
invalid degree and finite-formal-series preconditions.

`test_build.py` uses compiler simulations, without invoking TeX, for environment
isolation, path safety, publication, deterministic ZIP metadata, failed-build
cleanup, normal/optimized disagreements, and log rejection. It tests 43
acceptances and 120 rejections, including exact PDF/TeX archive identity. The
real builder separately invokes real TeX and the exact verifier.

## Regenerate without modifying the package

```
python -I -S -B code/regenerate.py --output /tmp/new-certificate.json --compare data/certificates.json
```

The output must be a new file outside the source/release package with an
existing nonsymlinked parent. Existing files, symlinked parents, and traversal
paths are rejected. The command derives the data from the exact algorithms,
checks against the optional comparison input, and creates output exclusively.
It never replaces the committed certificate.

## Deterministic PDF and source release

Choose a new output directory outside the package with an existing parent:

```
python -I -S -B build.py --output /tmp/report181-build-one
```

The builder performs these steps in private temporary storage:

1. Reject an existing output, symlinked path components, unexpected source
   entries, cache files, empty directories, or altered extracted-package hashes
2. Copy exactly the explicit source inventory
3. Run exact verification, mathematical corruption guards, and build guards in
   both ordinary and optimized isolated Python; require equal result objects
4. Compile with `pdflatex -no-shell-escape` until auxiliary files stabilize,
   with at least two passes and no more than six
5. Reject unresolved/multiply-defined labels or citations, rerun requests,
   overfull boxes, and missing characters; require a PDF signature
6. Create the complete file inventory and SHA-256 manifest, verify it, and
   produce a sorted ZIP with fixed timestamps and file modes
7. Publish Report181.pdf, Report181.tex, Report181.zip, and ARTIFACTS.json to a
   new directory without replacing existing outputs

`SOURCE_DATE_EPOCH=1790985600`, `FORCE_SOURCE_DATE=1`, UTC, and fixed ZIP date
2026-10-03 00:00:00 suppress changing metadata. TeX caches and the home directory
are private. Inherited TeX and Python configuration variables are removed. The
PATH and installed Python/TeX distributions are trusted inputs. The builder is
not a general sandbox for arbitrary hostile TeX or Python sources.

The release PDF and TeX are the exact bytes also stored in the ZIP. The ZIP
contains all package files, including source, frozen data, optional diagnostic
sources, the PDF, and generated verification/build JSON. `SHA256SUMS.json`
contains every regular package file other than itself; a manifest cannot hash
itself in this construction. The external `ARTIFACTS.json` hashes the three
distributable artifacts. SHA-256 detects accidental modification; replacement
of both content and manifest is outside this integrity guarantee.

Byte identity is promised for the same source and installed Python/TeX stack,
not across different TeX versions, fonts, engines, or operating systems. The
builder performs no network calls; package installation is never implicit.
`--extended` is retained as a harmless compatibility alias: the ordinary build
already runs all configured exact checks.

## Verify extraction and rebuild

Extract to a new directory without changing its contents, then:

```
python -I -S -B verify_manifest.py
python -I -S -B code/verify.py
python -I -S -B build.py --output /tmp/report181-rebuilt
```

An intact extracted release is accepted as input, with the old generated files
verified first and regenerated in private storage. Compare the output PDF, TeX,
and ZIP bytes against the original artifacts. Do not create virtual environments,
caches, optional outputs, or notes inside the extracted release: its inventory
is intentionally exact. Source files are not modified by the checks or build.

## Optional diagnostics

See `optional/README.md`. They require mpmath only when explicitly invoked.
Their frozen decimal tables are useful diagnostics; no finite-precision output
is used as a substitute for the report's proofs or the finite exact checks.
