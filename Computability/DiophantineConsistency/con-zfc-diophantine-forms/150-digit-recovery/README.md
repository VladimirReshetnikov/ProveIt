# Recovering signs from a binomial digit

## Delivered result

This package specifies one ordinary polynomial P in 247 unrestricted integer variables:

**P = R₁² + ··· + R₁₈₂² = 0.**

Every quadratic residual is printed in [article.pdf](article.pdf), Appendix A, and given exactly in [equation.json](equations/quartic247/equation.json). The [collected polynomial](equations/quartic247/expanded_polynomial.json) has degree 4, **4,755 nonzero monomials**, and **coefficient height 8,815**. All 247 coordinates occur.

The ordinary proof, composed with the retained pinned C222 calibration, establishes in ZFC:

**P has an integer zero if and only if there is a finite ZFC refutation.**

Equivalently, its lack of integer solutions is provably equivalent in ZFC to Con(ZFC). The construction does not prove either consistency or inconsistency. It does not assert a globally simplest equation or a variable-count record. The repository has quartics with fewer variables and large fixed coefficients. The objective here is a direct quartic with modest literal coefficients and a complete, reproducible finite specification.

The source snapshot is ProveIt commit **3ecd6a6cf53d47519228328567f45fb7ee9781d9**. Original incoming archive identities and hashes are in [SOURCE_LEDGER.json](SOURCE_LEDGER.json). No remote repository modification is part of this package.

## What is new

The new argument recovers the positive binomial digit before using the usual ceiling-sign certificates.

1. Restrict the radix to q = (6ζ+3)², so q ≥ 9.
2. Use the existing ratio q^(t+1) v = q^x to obtain x ≥ t+1, before interpreting the ceiling signs.
3. The genuine self-sized radix q = (BH₀)^x gives q ≥ 2^x and |B| < q/2.
4. The retained endpoint yields F²+t ≤ x−1. Thus all relevant binomial coefficients are below q/2.
5. The centered low-remainder equation forces B = binom(F²+t,t) > 0.
6. One product certificate rs = a²+b²+c(c+1), together with r+s = B−1 ≥ 0, restores both r ≥ 0 and s ≥ 0. The other missing sign follows.

Three scalar nonnegativity certificates, using nine coordinates, are replaced by one ternary product certificate and one square coordinate. An inherited deterministic comparison center removes one further coordinate. The ceiling remainder, formerly eliminated, is retained to keep the new product row quadratic. The exact final census is therefore 252 − 10 + 5 = 247, a net saving of five variables. The 76 final coordinate shears are transferred from an earlier packet with exact name matching; four additional residual operations improve the height.

Completeness is proved separately. The beta-CRT exponent can be made even, and cofinal lifts of the actual encoded representatives arrange H₀ ≡ 3 mod 6 while preserving the even dominant anchor. Thus the square restriction does not discard finite refutations.

The full fourteen-term canonical orientation argument is retained. The predecessor's selective nine-term sign-bootstrap schedule is not used.

## Exact comparison

All rows in this table concern unrestricted integer variables.

| Endpoint | Variables | Quadratic rows | Degree | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Common-remainder predecessor | 252 | 182 | 4 | 5,340 | 128,446 |
| New raw projected source | 247 | 182 | 4 | 5,310 | 128,446 |
| Delivered equation | **247** | **182** | **4** | **4,755** | **8,815** |
| Prior shared-residue endpoint | 260 | 186 | 4 | 4,770 | 9,191 |

The arithmetic and logical meanings are inherited except for the explicitly proved source changes. Factorials, powers and binomial coefficients are proof abbreviations; they are not primitives in the final polynomial.

## Read and verify

Start with [article.pdf](article.pdf) or its complete [LaTeX source](article.tex). The concise focused new proof is [proofs/NEW_ARGUMENT.md](proofs/NEW_ARGUMENT.md).

Python 3.10 or later and its standard library are sufficient for the main finite checks:

~~~sh
python3 -B verify.py
python3 -O -B verify.py
~~~

These commands are read-only. They verify the integrity manifest, inherited exact algebra, source delta, Horn factorizations, integral monic restorations, translations, final coordinate and residual inverses, every collected coefficient, every printed residual, metrics, and deliberate corruption controls. They also run the standalone finite checks for the separately labeled experiment.

To retain a new full receipt outside the package:

~~~sh
python3 -B verify.py --receipt /tmp/conzfc-verification.json
~~~

For a byte-for-byte rebuild of the inherited common-remainder endpoint in a temporary directory:

~~~sh
python3 -B verify.py --rebuild-parent
~~~

To regenerate the final finite files from the included raw source and frozen maps:

~~~sh
python3 -B code/build_final.py --write
~~~

To rebuild both PDFs, install a TeX distribution with the standard packages used by the sources and run:

~~~sh
bash build_report.sh
~~~

PDF bytes may vary with the TeX distribution. Regenerating a PDF changes its manifest entry; validate the algebra before deliberately updating an integrity manifest.

To evaluate a concrete tuple, put a JSON list of exactly 247 integers in tuple.json and run:

~~~sh
python3 -B code/evaluate.py tuple.json --expanded
~~~

This performs exact integer evaluation. It is not a decision procedure for existence of a zero.

## File map

| Path | Purpose |
|---|---|
| article.tex, article.pdf | Complete report, ordinary proof, all 182 residuals |
| report_inputs/ | Literal residual appendix and measured metric macros |
| equations/quartic247/ | Exact final equation, full expansion, metrics, coordinate map |
| certificates/ | 76 coordinate shears, four residual operations, historical name-transfer provenance |
| code/build_final.py | Deterministic reconstruction and comparison |
| code/check_final.py | Independent finite algebra and printed-specification checker |
| code/evaluate.py | Exact evaluation at a supplied tuple |
| source/equation247_weak/ | Raw new source, delta, projection and translation certificates |
| source/verify_composed.py | Independently reconstructed source delta and inherited algebra replay |
| source/build247_weak.py | Source producer retained for audit |
| source/inherited_common/ | Portable pinned direct predecessor and proof closure |
| proofs/ | New mathematical argument and attributed prior center/square arguments |
| review/ | Mathematical/algebra reviews and actual verification receipts |
| experiments/three_parameter_calculus/ | Separate, unsuccessful source-calculus compression attempt |
| SOURCE_LEDGER.json, NOTICE.md | Provenance and attribution |
| MANIFEST.sha256.json | SHA-256 hashes of all final package files except itself |

## Verification scope

The new proof is an ordinary unbounded mathematical proof using the named inherited interfaces, not a newly kernel-checked end-to-end Lean/Rocq formalization. The retained logical endpoints are KEndpoint.c222_iff_zf_refutation and ConstructibleChoice.zf_refutation_iff_zfc_refutation. The finite scripts do not recompile the complete upstream proof environment, and sampled modular checks in the experiment do not replace its general proof.

The mathematical and algebra reviews were conducted as separate reviews within the AI-assisted research workflow. They are not represented as external human peer review.

The main independent algebra checker imports no producer or eliminator. It uses exponent-vector monomials and binomial shear expansion, checks forward and inverse maps and both matrix inverse products, and parses the actual TeX formulas back into polynomials. Six source corruption controls and eight final algebra corruption controls are rejected with and without Python assertions.

## Separate experiment

The three-parameter-calculus note replaces a four-parameter implicational schema by K, S and Peirce, and uses an unbounded modular inverse in a saturation constraint. Its literal 521-step Hilbert derivation is checked independently.

The measured result has 231 **nonnegative** variables, 183 quadratic rows, degree 4, 6,369 terms and height 83,899,166. It does not beat its own 229-variable nonnegative parent. Its domain and compiler differ from those of the preferred 247-integer equation. Its standalone finite checks are included; regenerating it through its different full inherited compiler requires the parent archive identified in its PARENT_PIN.json.

## License

The inherited repository's MIT No Attribution license is retained in [LICENSE](LICENSE). See [NOTICE.md](NOTICE.md) for source attribution and the boundary between the new argument and reused methods.
