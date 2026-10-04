# Independent scoped review of the BCH inverse-domain correction

**PASS, with no requested correction.** The replacement paragraph and numbered retained counterexample in `02_formal.tex` are mathematically sound. The selected formal word-coefficient proof and the elementary finite-computation claims also pass the challenge below. This is not certification of the whole combined article, all analytic claims, the Lean development, or the supplied computational evidence.

No repository file was changed. No author, supplied, archived, frozen, copied predecessor helper, or build was executed or imported. The root's fresh71-line helper was read in full as text only. My tool use was limited to reading source, an immutable Git excerpt, the complete correction diff, and fresh byte/span hashing.

## Exact read scope and pins

All TeX paths below are relative to `Algebra/BakerCampbellHausdorff/docs/combined/tex/`. The corrected `02_formal.tex` is the working-tree snapshot reviewed here; the other listed sources have their independently recorded complete-byte hashes. Inclusive read ranges are exact.

| File | Lines actually read | Whole-file SHA256 |
|---|---|---|
| 01_scope.tex | 1–90 | c8691473841101bd6bb4f845e3c203a99b2fd42f641740d0a086760327c4c113 |
| 02_formal.tex | 1–266, complete corrected file | 42d4f8b9d9c5b0a4b135ae33212b852dc4114f512443432d7b67d06fd417592a |
| 14_computation.tex | 1–143, complete file | 0161377277b922b3d75287760e035a0f89dc7e7e422c86165a8f65b8f2e471c6 |
| 07_convergence.tex | 1–90 and195–260 | 826f02bc7f31be657dafc81cd2f5b982fa3bb67eaa5b1268889d0f6e62ff0a0d |

For the partial-file ranges, the exact byte-span SHA256 values are:

* `01_scope.tex:1–90`: f103fea8a4a0bd2c468d2bfa7d696d0a1ae3499bd0ae0297df2fe5d12a9a1254;
* `07_convergence.tex:1–90`: c9014b74dc0a9cb9b08b13e703a150f246a6ce9e9fed46afff6f1c89f6e0ba54;
* `07_convergence.tex:195–260`: df0ff09e93930d1bdb27900854cbb4aef1671ae4560881c0a3c6ccc10856805f.

I also read the entire working-tree correction diff and independently read immutable `ad52ef11e:.../02_formal.tex` lines73–83, containing the former paragraph. That old file has249 lines, Git blob `bdc5879a10e359503cee63596c53222e2d4040fe`, and SHA256 `48a2407360e2d8e6f5105f138410200c0df4522f03117fe8631f0975df22b6ed`.

The complete helper read was `/tmp/review_bch_ad52ef11e.py`,71 lines, SHA256 `396513caa931ea35297e3d2f8bc7c33cc4480ff201aa29105411b07447ae372b`. These inspected bytes were subsequently frozen unchanged. I did not execute it or independently replay its CSV comparisons.

I then read the complete frozen root review `/tmp/review_bch_ad52ef11e.md`, SHA256 `0214cf8b62a733875ef7fb8a467ae48257e228853a63f2639d6a2e4caf4d0d74`, and authenticated its receipt bytes, SHA256 `b44a6287e6ab3a69e3611c173c251fa3e6e05a0e1d9888a21ff19f5bb4fdf3b6`. Its finite-coefficient, denominator, and correction conclusions agree with this challenge. Its larger provenance scope, reported checks, and PDF build remain root-attributed evidence rather than independently repeated work.

## Analytic correction and retention

The original phrase “on those domains” follows convergence of exp for all A and convergence of the Mercator logarithm for norm U<1. It does not justify the global inverse composition log(exp A)=A. The retained complex scalar example A=2*pi*i has exp A=1, U=0, and Mercator log1=0. Both defining series converge at their selected arguments, yet the proposed unrestricted inverse equality fails.

The correction gives separate sufficient domains: exp(log(1+U))=1+U for norm U<1, and log(exp A)=A for norm A<log2. The selected Mercator and small-logarithm proofs establish precisely these statements. The bound on A ensures norm(exp A−I)<=exp(norm A)−1<1 and keeps the branch fixed along tA. For real Banach algebras the same differentiated argument can be read on a real interval containing[0,1]; no complex scalar action on a real algebra is necessary.

For commuting A,B with norm A+norm B<log2, their individual norms and norm(A+B) meet the local hypothesis. The absolutely convergent exponential binomial identity gives exp(A+B)=exp A exp B, and the displayed local additive logarithm law follows. Applying the same local statement to A and−A proves the displayed sign law. No additional assumption norm I=1 is needed for these positive-degree estimates.

The numbered remark retains the former wording, explains its false global reading, and records the counterexample. It distinguishes that defect from the unaffected formal inverse theorem. The replacement gives sufficient local hypotheses and does not claim they are optimal.

## Formal and finite arithmetic interfaces

The characteristic-zero hypothesis in the selected scope source permits rational coefficients. In the degree completion, every coefficient of a substitution of a positive-degree series depends on finitely many terms. This justifies the formal inverse proof independently of analytic convergence or injectivity. The every-word formula follows by cutting a word into nonempty consecutive factors of exp(X)exp(Y)−1; cuts with more pieces than the word length vanish. A binary word of length n has exactly2^(n−1) possible cut patterns. These facts give an exact terminating rational algorithm for each requested finite cutoff.

The proposed uniform denominator bound also follows directly. For one contributing cut of a length-n word, its denominator is

```
k * product_i(r_i! s_i!),  sum_i(r_i+s_i)=n, 1<=k<=n.
```

The factorial product divides n! by the integer multinomial coefficient, while k divides lcm(1,...,n). Therefore every summand, and hence every resulting word coefficient, has reduced denominator dividing

```
n! * lcm(1,...,n).
```

For all degrees at most a fixed positive N, the single bound N!*lcm(1,...,N) suffices because it is a multiple of each lower bound. The constant BCH coefficient is separately zero. Thus equality of finite truncated rational word polynomials is decidable by finite exact integer/rational calculation. Evaluating this finite homogeneous sum through degree N at fully supplied finite rational polynomials or rational matrices remains a finite rational calculation. A total computable reduction of arbitrary halting to that fully supplied equality predicate would compose with this decision procedure to decide halting, so the root's stated obstruction is correct. This does not decide equations with existential integer unknowns or an unbounded history parameter. Nor is it a statement about exact equality of arbitrary real numbers, convergence of an unbounded series, or a fixed-arity paid integer compiler of uniform small size. The word and cut counts grow with the cutoff.

## The fresh path-matrix check is algebraically independent

For a target word of length n, the helper creates(n+1)-dimensional strictly upper-triangular matrices, placing a1 on edge(i,i+1) in X or Y according to that target letter. For any monomial, its entry(0,n) vanishes unless it has length n and follows exactly that letter sequence; in that one case it equals1. Thus this matrix entry extracts the coefficient of one specific free word. This avoids the usual danger that arbitrary selected matrices collapse distinct words or commutators.

Both matrices and exp(X)exp(Y)−I are strictly upper triangular in their positive-degree parts. Powers beyond n vanish. The helper's finite exponential and logarithm sums therefore compute the exact coefficient, including zero coefficients. Its upper-triangular multiplication bounds preserve all contributing entries. Enumerating every binary word in degrees1 through6 gives126 separate coefficient checks. The helper's CSV checks of reduced fractions and denominator divisibility are a different, explicitly finite audit; they do not recompute every degree7–12 coefficient.

I checked this algorithm and its scope by inspection, not by running it. The selected computation chapter likewise distinguishes finite checks from all-order theorems and specifies associative, right-nested, and Lyndon encodings separately. I did not audit the supplied dictionaries, bracket generators, external Lyndon-basis theorem, Hopf/Lie proof, or the reported historical verifier runs.

The correction and these finite arithmetic observations provide no operation-count improvement for the separate universal Diophantine compiler work. The unread portions of the article, its full provenance and archive history, PDF builds, and Lean proof/axiom status remain outside this independent review.
