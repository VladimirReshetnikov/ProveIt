# Report144 exact reproducibility companion

This directory contains a standalone Python-standard-library certificate for the strict enclosure

\[
\frac{527}{1000}<r_*<\frac{79}{125},\qquad r_* = \lim_{n\to\infty}W_n^{1/n}.
\]

Every certificate calculation uses integers or `fractions.Fraction`. There are no floating-point calculations, tolerances, or timing fields in the certificate or its verification summary. Python 3.9 or newer is required. No third-party package, network connection, local helper-module import, or original PDF is required.

## Run

From this directory:

```sh
python -I verify_certificate.py
python -I -O verify_certificate.py
python -I test_verifier.py
python -I -O test_verifier.py
```

`python` must refer to a trusted Python 3.9+ installation; use `python3` instead if appropriate. `-I` is mandatory and is checked before filesystem-resolved imports. It ignores Python environment variables, excludes the working and script directories from module search, and disables the user site. `-O` is supported: no mandatory condition uses `assert`.

Successful verification emits a deterministic JSON summary and exits with status 0. Failure exits nonzero. Verification normally performs no file writes. The fixture is data only; no code is loaded from it. Both exact computational routes are rerun for every verification.

For a fresh output copy on a system supporting secure descriptor-relative file creation:

```sh
OUT=$(mktemp -d)
OUT=$(cd "$OUT" && pwd -P)
python -I verify_certificate.py --write-output "$OUT"
cmp fixtures/rate_certificate.json "$OUT/verified_certificate.json"
```

The explicit output directory must already exist, have a canonical resolved path, contain no symlink component or `..`, and lie outside this companion's source tree. The fixed output basename is `verified_certificate.json`; no filename argument is accepted. Existing files, symlinks, and hard links are never overwritten. POSIX descriptor-relative `O_NOFOLLOW`/`O_EXCL` operations prevent traversal through symlinks during output creation. Systems lacking those operations fail closed for `--write-output`; read-only verification and stdout summaries still use portable standard-library facilities. The test suite explicitly reports that case rather than claiming its output-containment tests passed.

An alternate fixture can be checked without changing the bundled one:

```sh
python -I verify_certificate.py --fixture /absolute/path/to/candidate.json
```

This is a validator, not a permissive importer: a structurally valid candidate must match the independently regenerated complete certificate exactly.

## Files

- `verify_certificate.py`: independent regeneration, strict fixture validation, and exact bound checks
- `fixtures/rate_certificate.json`: all 101 reduced rational probabilities, a six-term exact prefix, a digest of the entire vector, integer square-root floors, exact comparison quantities, and closed typed checks
- `test_verifier.py`: adversarial schema, mutation, isolation, and output-containment tests
- `SCHEMA.md`: exact fixture field/type and rational-encoding specification
- `PROVENANCE.md`: mathematical/computational methods and provenance

The all-vector SHA-256 is

```
f6910ee2606f2272b4293f20e2d923961d6245e64743e112bc23c8cdc777c2f7
```

Its input is each reduced numerator and denominator in lowercase hexadecimal, joined by `/`, one rational per line, with a final LF. No `0x` prefixes or leading zeros are present. The fixture JSON has an independent file hash, which is different from the rational-vector hash.

## Independent exact routes

With `W_0=1`, the verifier computes

\[
 W_n=\sum_{k=1}^{n}W_{k-1}W_{n-k}\,b_{n,k},
\]

where

\[
 b_{n,k}=\binom{n-1}{k-1}
 \int_{(k-1)/n}^{k/n}t^{k-1}(1-t)^{n-k}\,dt.
\]

The first route computes every weight without symmetry reduction, using the exact integer binomial tail

\[
 T_{n,k}(a)=\sum_{j=k}^{n}\binom nj a^j(n-a)^{n-j},\qquad
 b_{n,k}=\frac{T_{n,k}(k)-T_{n,k}(k-1)}{n^{n+1}}.
\]

The second route independently integrates the expanded polynomial, using rational endpoints and the alternating antiderivative. It checks all 2,550 symmetry-distinct polynomial weights against both corresponding binomial-tail weights and computes its own probability vector. Every probability in the two vectors must agree exactly. Thus all 5,050 weights in rows `n=1,...,100` are covered, as are all 101 probabilities.

The checked prefix is

\[
1,\quad1,\quad\frac34,\quad\frac{83}{162},\quad
\frac{55537}{165888},\quad\frac{11049709}{51840000}.
\]

## Exact finite certificate

Set `m=N=101`, `q=527/1000`, `b=79/125`, `x=1/b=125/79`, and `S=10^12`. The program proves the exact finite inequalities

\[
 W_{100}>16\cdot101^2 q^{101},
\]

and, for every `n=0,...,100`,

\[
 s_n=\operatorname{isqrt}((n+1)S^2),\qquad
 s_n^2\le(n+1)S^2<(s_n+1)^2.
\]

It evaluates the rational polynomial

\[
 P_{\rm upper}(x)=\sum_{n=0}^{100}\frac{S W_n}{s_n}x^n
\]

by Horner's rule and verifies

\[
 4xP_{\rm upper}(x)<\frac{95111}{1000}<101.
\]

Because `s_n/S` is a positive lower bound on `sqrt(n+1)`, the rational polynomial is an upper bound on `P_101(x)=sum W_n x^n/sqrt(n+1)`.

## What is and is not established by running the code

The code establishes the finite rational recurrence values and the displayed exact comparisons. Turning those comparisons into bounds on an infinite-sequence limit requires the accompanying Report144's analytic results:

1. Existence of the positive nth-root rate `r_*` and `R=1/r_*`
2. The global normalized-kernel bound `alpha_(i,j) <= 1`
3. The lower theorem `[W_(m-1)/(16m^2)]^(1/m) <= r_*`
4. The Catalan-majorant theorem `r_* <= 1/x_N`, where `4 x_N P_N(x_N)=N`

With those theorems, the first comparison makes the lower bound strict. The upper comparison gives `x<x_101<=R`, so the upper bound is strict as well.

This program does not prove those analytic theorems or the report’s pointwise-equivalent and consecutive-ratio theorems, validate their hypotheses beyond the finite range, establish a coefficientwise correction expansion, certify a longer conjectured decimal expansion, or establish novelty. A hash alone is not a proof: the mandatory full recomputation is what rejects altered numerical semantics even if a candidate's vector and file hashes are updated.

## Adversarial tests and security boundary

The suite tests unknown, missing and duplicate fields; booleans in integer fields; integers in boolean fields; malformed/nonreduced rational encodings; JSON floating-point and nonfinite tokens; inconsistent lengths; false check flags; changed parameters and exact comparison quantities; and changed probabilities with recomputed hashes. It also verifies source/fixture preservation, no overwrite, symlink and path containment, and malicious startup files under both normal and optimized isolated Python.

The startup tests put hostile `sitecustomize.py`, `usercustomize.py`, and standard-library-named files in both the working and script directory, and set hostile `PYTHONPATH`, `PYTHONHOME`, and `PYTHONSTARTUP`. They confirm that the malicious code is not executed and that normal/optimized outputs agree byte for byte. They do not certify a compromised Python executable or a modified system standard library/site installation. Run the supplied files with a trusted interpreter; inspect or authenticate the manifest through a trusted channel when provenance matters.
