# A single norm for factorial and digit certificates

Prepared for Vladimir Reshetnikov and the ProveIt research program, 25 October 2026, with AI assistance.

Start with **report/report.pdf**. Its complete editable source is **report/report.tex**. The report prints all 181 residuals of the principal equation and proves the new arithmetic reduction.

## Principal result

The package supplies a fixed polynomial

    P245(X0,...,X244) = R0(X)^2 + ... + R180(X)^2

over unrestricted integers. Every residual has fixed integer coefficients and degree at most two. The complete residual list, full collected expansion, plaintext equation, and coordinate labels are in `direct/equation/`.

| Measure | Latest inspected direct parent | New principal equation |
|---|---:|---:|
| Integer variables | 252 | **245** |
| Quadratic residuals | 182 | **181** |
| Total degree | 4 | **4** |
| Collected monomials | 5,340 | **5,304** |
| Coefficient height | 128,446 | **128,446** |

The ordinary mathematical proof, composed with the retained C222/ZF/ZFC syntactic calibrations, proves in ZFC that the absence of an integer zero is equivalent to Con(ZFC). The construction does not depend on a consistency assumption. The final equation contains no variable exponents, factorial primitive, binomial primitive, unspecified coefficient, or unexpanded universal-polynomial parameter.

This is an improvement of the direct numerical proof-calculus family. Compact native-coefficient constructions with fewer unknowns have different degree and coefficient tradeoffs. No global simplicity optimum or literature-wide priority is claimed, and this package does not supply a newly compiled end-to-end Lean/Rocq proof term.

## Mathematical contribution

The existing common norm controlled eleven normalized low binomial remainders. The new construction also puts the factorial ceiling error into this norm. Two quadratic rows

    B*d = M,
    F*M - d*V - e = 0

and the shared bound give `|F*B-V| < |B|/2`. This removes all three initial sign certificates, including nine private coordinates; it introduces only `d,e`.

An odd multiplier `H=1+2*sum(a_i)` is nonzero before signs are known. Signed-base power recovery and an already present denominator-ratio identity force a sufficiently large radix. A separate estimate treats `F=0`. Once `B=binom(F^2+t,t)` has been recovered, the new rounded-factorial identity forces `F=t!` and recovers all deleted signs.

The report proves the standalone identity for every integer `t>=4`:

    |F - (F^2+1)^t/binom(F^2+t,t)| < 1/2  iff  F=t!.

The principal source uses `t>=16`, where the canonical error is smaller than `1/32` and fits the shared norm with the other eleven remainders.

Changing the multiplier H changes the semantic witness construction. The proof is an equivalence of zero existence through finite refutations, not a coordinate bijection between all old and new source zeros. The later constrained monic eliminations and integer translations have exact inverse certificates. The projection also discards 112 unused coordinates, which may be restored to zero; this deletion preserves existence of zeros without giving a bijection of all raw assignments.

## Compact companion

`compact/equation78_degree454.json` is a separate ordinary polynomial in ten **strictly positive** integers, with exact total degree **454** and **78** live binary arithmetic operations. It uses the entire authenticated fixed coefficient tuple supplied in `compact/coefficients/`.

Its new proof recovers a product of two radicands as a square, folds the main Pell index, and only then separates the first Pell square. It trades one operation for six fewer degrees relative to the inspected 77-operation degree-460 equation, or two operations for ten fewer degrees relative to the matched 76/464 parent. It is not an unrestricted-integer equation and must not be compared to the principal construction without keeping the domains distinct.

## Reproduce

Python 3.10 or newer and the standard library suffice for the algebraic checks:

```sh
python3 -B verify.py
python3 -B verify.py --rebuild --receipt /tmp/conzfc-replay.json
```

The root verifier independently recomputes all collected coefficients and checks that the typeset and plaintext residual specifications exactly match the literal equation. It runs the component verifiers in ordinary and optimized Python. `--rebuild` additionally reproduces all 16 direct JSON artifacts byte for byte in a fresh temporary directory.

The direct checker authenticates 88 retained parent files, checks 18 Horn factoring edits, 202 integral monic eliminations, the final coordinate translation, and every collected quartic coefficient. It rejects six deliberately corrupted mathematical artifacts. The compact verifier checks every live gate through exact polynomial cuts, the whole coefficient tuple, and the full highest homogeneous form. These finite checks supplement the unbounded proofs; they are not a search for zeros or a consistency decision procedure.

To build the report using a standard TeX Live installation:

```sh
sh build_report.sh
```

The appendix generator reads the final JSON polynomial. It introduces no new mathematical constants. Rebuilding may change PDF metadata; the supplied PDF has its own final hash in `MANIFEST_SHA256.json`.

## File map

- `report/`: full article, all LaTeX inputs, literal residual appendix, and PDF.
- `direct/`: main polynomial, its constructor, independent checker, exact evaluator, finite transformation certificates, and retained proof closure.
- `direct/proofs/BOOTSTRAP_PROOF.md`: expanded ordinary proof, edge cases, and the rounded-factorial theorem.
- `compact/`: ten-positive companion, full definitions, proof, fixed coefficients, generator, and independent checks.
- `verification/`: root checks, report checks, and internal mathematical-review receipts.
- `RESULTS.json`: machine-readable results, comparison boundaries, and proof status.
- `SOURCE_SNAPSHOT.json`: exact repository pin and hashes of all eight inspected incoming archives.
- `INTEGRATION.md`: suggested integration boundaries and theorem names.
- `MANIFEST_SHA256.json`: final file identities.

## Source boundary and licensing

The immutable comparison snapshot is ProveIt commit `3ecd6a6cf53d47519228328567f45fb7ee9781d9`. The immediate direct parent is the incoming `ConZFC_Common_Remainders_Radix47_2026-10-25.zip` archive. The compact parent is the incoming `ConZFC_Centered_Residues_2026-10-25.zip` archive.

Inherited source files, formal-interface excerpts, licenses, notices, and identities are retained. The complete mathematical argument is an ordinary proof formalizable in ZFC; it is not represented as a fresh full formal-assistant build. Separate agent reviews in this package are internal AI-assisted reviews, not external human peer review. New material follows the repository's MIT No Attribution license.
