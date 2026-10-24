# Independent audit: joint positivity compression

## Finding

PASS. The 28-integer octic and the 26-integer degree-sixteen companion are exact existential reductions of the pinned 30-integer octic. The latter is a variable/degree tradeoff, not an octic improvement. No global minimality, priority over the literature, or new proof-assistant certificate is asserted.

The elementary lemma, for integers x,y, is

    x>0 and y>0 iff there exists t in Z with
    xy-(t^2-x-y+1)^2>0.

For soundness, positivity forces xy>0; if x=-a,y=-b with a,b>=1, then the subtracted square is at least (a+b+1)^2>ab, a contradiction. For completeness let N=x+y-1, so 1<=N<=xy. With m=floor(sqrt(N)), either m^2 or (m+1)^2 differs from N by at most m. If N is a square the error is zero; otherwise its square is at most m^2<N<=xy. This establishes strict positivity, including boundary cases x=1 or y=1.

The convention Pos(p,q,r)=1+p^2+q^2+r(r+1) is correct for unrestricted integers: r(r+1)>=0, and for n>=1 the positive integer 4n-3 is 1 modulo 4 and is not of the excluded three-square form. In a three-square representation exactly one summand is odd and the other two are even. Rearranging gives the stated Pos representation of n.

## Source relation and dimensions

The exact source is SignAndNorm's `quartic42/companions/octic30.json`, SHA-256 91ee2d3d9a97d386fa2e8b939884d6cd846e866bb45b1efe945f11873e27b72c. All 27 Q42X rows, after the complete 42-coordinate restoration, are independently checked to become zero or one of the 15 source30 rows; each surviving row occurs exactly once.

The source's last three residuals assert strict positivity of precisely

    x=F alpha,
    y=F(beta J+1-F-alpha),
    z=eta(1-V+jc+hE-eta).

All remaining twelve arithmetic residuals are retained exactly. The new octic replaces the first two three-witness Pos rows by one four-witness joint-positivity row, retaining the third guard. Therefore 30-6+4=28 variables and 15-2+1=14 residuals. Every residual has degree at most four, and the final sum of squares has coefficient [a^4 f^4]=1. Its degree is exactly eight, even after specialization to the actual fixed coefficients; its expansion has 551 terms over the coefficient ring.

The nested construction replaces all nine positivity witnesses with two nearest-square roots and three Pos witnesses. Hence 30-9+5=26 variables and 15-3+1=13 residuals. The new residual has degree eight and coefficient [pair_root^8]=-1; no other residual uses pair_root. Its sum of squares therefore has coefficient [pair_root^16]=1 and exact degree sixteen. The new guard has 231 expanded terms over the coefficient ring.

Existential maps are explicit: select nearest-square roots, then represent each remaining strictly positive result using Pos; conversely, positivity of Pos and repeated application of the lemma recover the deleted positive quantities and their original Pos witnesses. This is not a polynomial identity between old and new final sums of squares, nor a bijection of all auxiliary witnesses.

## Complete coefficient tuple

`BINDING.json` is the release-side binding for both new equation packets. All four actual source34 payloads are supplied under `coefficients/`, as minimal unsigned little-endian `.bin` files and byte-exact original `.bin.gz` copies. The map is beta->beta, K0->K, MC->MC, MF->MF_source. The last port is already shifted by beta and must never be replaced by MF_native.

The radix is B=2^1064921 and beta=B-1. All four coefficients come from the SAME compiler manifest. No numerical ports have been spliced. The total raw payload size is 532,479 bytes and original gzip total is 10,466 bytes.

The independently authored checker reconstructs every coefficient directly from the published bounded recipe and ordered 943-tile data, and compares the resulting integers to all actual payloads. It also verifies raw and compressed hashes, decompression identity, lengths, bit lengths, and minimal integer encoding. No upstream builder or checker is imported or executed. This audit does not newly prove that the 943 tiles simulate K215 or reprove the inherited unbounded Pell/compiler transfer theorem. Those mathematical dependencies remain explicitly inherited from the pinned source proof. The four large numerals are fully materialized; no halt-dependent or unknown coefficient is used.

## Replay and packaging

From any working directory, run:

    python path/to/integer_system_audit/independent_check.py
    python -O path/to/integer_system_audit/independent_check.py

The checker requires SymPy (tested with 1.14.0); it parses a restricted arithmetic AST itself and does not evaluate source strings. The sibling directory `integer_system` must contain `octic28.json`, `degree16_26.json`, and `inherited/octic30.json`. Both receipts are included. The checks use explicit exceptions, not removable asserts.

The two new equation packets' live relative manifest, compiler-manifest, transfer-proof, and payload paths now resolve to the supplied audit binding and actual coefficient files. The checker verifies every resolved path against both the release binding and the inherited symbolic port map, preserving the complete tuple and shifted-mask convention. The inherited source JSON remains byte-exact.

The finite nearest-square regressions are diagnostics only. Universal correctness rests on the proof above and the source theorem. The final ZFC theorem follows by composing (i) these elementary witness transformations, (ii) exact source30/Q42X elimination and square-guard relocation, (iii) the pinned Q42 sign-recovery theorem and (iv) its stated compiler/calibration theorem. The result does not claim that ZFC proves Con(ZFC); it proves the equivalence of this polynomial's lack of integer zeros with Con(ZFC).
