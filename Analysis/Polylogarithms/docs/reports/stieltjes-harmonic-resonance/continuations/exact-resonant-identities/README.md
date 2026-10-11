# Exact Resonant Identities Beyond the Diagonal

Research continuation prepared with ChatGPT for Vladimir Reshetnikov's ProveIt project, 11 October 2026.

The report continues the canonical manuscript and the eleven incoming archives present at commit **5a790187c8e186e41e2b990b4941cb7a1a3c7b6b**. It contains complete proofs, exact formulas, an external sign correction, fifteen proposed research questions, and independent reproducible verification. It is supplied for review and integration; the inspected repository was not modified.

## Start here

- `Exact_Resonant_Identities.pdf` — the complete article.
- `Exact_Resonant_Identities.tex` — self-contained TeX, including its bibliography.
- `article.tex`, `preamble.tex`, `sections/`, and `references*.tex` — modular sources for integration.
- `integration/INTEGRATION.md` — suggested destinations and precise status updates.
- `claims.json` — theorem-level contribution and scope ledger.
- `provenance/` — pinned source records, archive hashes, and dependency notes.
- `verification/`, `results/`, and `certificates/cayley/` — replay scripts and exact certificate data.
- `SHA256SUMS` — checksums of delivered package files.

## Mathematical contributions

### 1. Independent directions at ordered depth four

The article evaluates the entire Laurent expansion through the finite part of the common-shift ordered Hurwitz function at `(1,1,1,1)` along every straight ray whose four prefix slopes are nonzero. The necessary quadratic depth-two and linear depth-three regular jets are explicitly reduced to ordinary Hurwitz/Stieltjes data and three additional coordinates beyond the earlier ordering function `eta(a)`.

All retained coordinates have absolutely convergent series, triangular shift laws, and a three-ray reconstruction. Their displayed coefficients cancel precisely on the equal-trailing-slope locus. This is a proved spanning normal form and a formal cancellation statement, with no assertion of arithmetic independence or arithmetic minimality.

### 2. Coincident reflected Stieltjes and polygamma products

A holomorphic completed cotangent–Hurwitz transform evaluates every coordinate finite-part integral of one Stieltjes derivative times a cotangent derivative. The resonant subtraction keeps the **whole parameter-dependent polynomial amplitude**, which is necessary to recover the finite harmonic-number corrections.

The derivative-polynomial algebra then evaluates arbitrary finite products of coincident reflected polygamma factors. Explicit consequences include reflected cubic and quintic moments, a cubic difference, all odd reflected digamma moments, and log-Gamma moments with harmonic-number constants. Rational partial fractions extend the finite reduction to repeated seams.

The endpoint coordinates are fixed as `x` and `1-x`. These formulas concern specified finite parts, not ordinary improper integrals. The generic unreflected cubic Tornheim coordinate remains unevaluated.

### 3. Raw harmonic powers with a continuous outer shift

For `F_p(s,a) = sum_{n>=0} H_n^p/(n+a)^s`, the inner harmonic numbers are unshifted. Every principal Laurent coefficient and the finite part at `s=-m` is polynomial in the outer shift `a`, of degree at most `m+1`. The article gives a finite Bernoulli formula for every principal coefficient and a finite multiple-polylogarithm recursion for every finite part.

At `a=1/2`, **every nonpositive even spectral point is regular**, for every positive integer power `p`; the values lie in the ordinary convergent multiple-zeta algebra without requiring Euler's constant. Complete expansions at zero, explicit square/cube/fourth-power formulas at `-1` and `-2`, and normalized shift antiderivatives are included.

The global Mellin remainder disappears from the principal part and finite part, but generally returns at the next regular spectral coefficient. Foundational unshifted raw-power continuation is explicitly credited to earlier literature.

### 4. A complete-Cayley obstruction for the bounded S6 search

The inherited integer separating functional also annihilates the entire intersection of the **full convergent Cayley shuffle ideal** with the bounded target space. The resulting theorem is

`T not in J_7^- + span_Q(R_4)`.

Here `J` has no depth restriction and allows arbitrary shuffle multipliers; `R_4` is the precisely enumerated inherited family of 5,131 additional rows. The kernel theorem and depth preservation justify checking all 2,546 bounded basis differences. The exact nonzero target pairing is

```text
-186660627289236812620583691130496682078843750753489297279472069700354208
```

The formal target satisfies `H(T)=128588 i R_6`. **The period conjecture `R_6=0` remains unresolved.** This result neither disproves S6 nor proves that every conceivable proof requires depth five. The revised S8 candidate is also unresolved.

### 5. A precise external correction

Section 6 corrects the sign of the first harmonic Stieltjes term in equation (22), printed page 5, of Lo Ho Tin's **arXiv:2507.03058v1**. Under its own Laurent convention, the printed plus must be a minus. The article proves an ordinary absolutely convergent identity for every logarithmic moment that makes this sign explicit, and checks consistency with the preprint's equation (11).

No false theorem was identified in the selected incoming cubic/coincident material. The audit distinguishes this external formula correction from safeguards against possible normalization mistakes.

## Build

Tested with Python 3.12.14, pdfTeX 1.40.25, mpmath 1.3.0, and SymPy 1.14.0. The document uses ordinary AMS/LaTeX packages, Latin Modern fonts, `mathrsfs`, `geometry`, `microtype`, `hyperref`, `bookmark`, `booktabs`, `longtable`, `enumitem`, and `fancyhdr`.

From the package root:

```sh
python3 build.py
```

The build script inlines the modular sources and compiles the standalone file three times, writing the final PDF at the package root and intermediate files under `build/`. It requires no network access. To regenerate only the standalone source:

```sh
python3 build.py --source-only
```

The standalone file can also be compiled directly with `pdflatex` three times. Its contents do not depend on any external repository file.

## Verification

Install the pinned optional verification dependencies if needed:

```sh
python3 -m pip install -r requirements.txt
```

Exact checks:

```sh
python3 verification/verify_all.py --exact-only
```

All supplied exact and numerical checks:

```sh
python3 verification/verify_all.py
```

Individual replays:

```sh
python3 verification/verify_ordered_exact.py
python3 verification/verify_ordered_numeric.py
python3 verification/verify_harmonic_symbolic.py
python3 verification/verify_harmonic.py
python3 verification/verify_reflected_collision.py --higher-stieltjes --output results/reflected_collision.json
python3 certificates/cayley/code/verify_complete_cayley.py
```

The complete Cayley verifier uses only the standard library and takes approximately half a minute in the preparation environment. The full numerical runs take longer, especially the reflected higher-Stieltjes integration. The scripts print progress. Quick options on the ordered and harmonic scripts overwrite their usual receipts, so use the full commands to reproduce the shipped full-run records.

### Recorded results

| Branch | Exact checks | Independent numerical checks |
|---|---|---|
| Ordered depth four | 23 symbolic assertions; corrupted-coefficient rejection | 4 directional finite parts and 4 shift checks; maximum discrepancy about `6.54e-34` |
| Reflected products | 15 exact polynomial assertions | 30 checks at 50 decimal digits; maximum discrepancy about `4.38e-47` |
| Harmonic powers | 171 symbolic assertions | 72 Laurent coefficients at 58 decimal digits, including stronger-cutoff replays; maximum discrepancy about `3.41e-41` |
| Complete Cayley ideal | 5,131 regenerated rows, 2,546 ideal basis differences, 780 Eulerian/convention cases, 2,150 shuffle-product checks | No floating-point arithmetic is used in the certificate |

The numerical figures are **observed discrepancies, not rigorous error bounds**. The analytic proofs establish the infinite families. The exact certificate establishes formal-algebraic nonmembership. Neither the scripts nor the report are a proof-assistant formalization.

`results/runner_exact.json` records the packaged exact replay. The numerical branches were also replayed independently during preparation; their complete records are in `results/`. Replaying changes timing fields, and therefore can change receipt checksums. The Cayley verifier separately checks the integrity of the immutable source modules and functional data before doing any algebra.

## Source and status discipline

The source manifest distinguishes the canonical snapshot, incoming archives, exact upstream formal-algebra modules, and external primary literature. The two reused Cayley modules retain their original bytes and Git-blob hashes. The top-level manuscript section adapts the certificate's presentation and relative command path, while the certificate subdirectory retains its self-contained contribution layout.

No claim of global priority is made for classical ingredients or for every special case. No claim of arithmetic independence is made. S6, the revised S8, and the generic unreflected cubic Tornheim reduction retain their open status.
