# Two exact coefficient savings in complete binary recoders

The frozen first-coefficient identity applies twice to the actual ordinary-input recoder: once in its geometry core and once in its prescribed AND core. Each removes one multiplication. The inline radix16 certificate therefore costs **128=65M+63A**, and its complete SOS polynomial costs **229=99M+130A**, with the same49 positive auxiliaries and34 comparisons.

The same two literal cones occur inside the newly reviewed exact-width Grill loader. Its complete polynomial becomes **16,289=4,994M+11,295A**, on the same3,217 positive witnesses and48 comparisons. This is the same entire polynomial as its16,291-operation parent on every supplied tuple. The measured corrected Genera table is still the nonuniversal reject-all example; no universal operation bound follows.

The [source](native_binary_recoder_factored128.py) and [receipt](native_binary_recoder_factored128.json) contain four selected complete sources. Every current source, interface and ledger is explicit. Unchanged parent semantics and old native counts are labeled historical provenance. Neither the original recoder nor the frozen exact-width packet is edited.

| Selected form | Certificate M+A | Comparisons | Positive auxiliaries | Complete polynomial M+A | Degree |
|---|---:|---:|---:|---:|---|
| Inline width4 |65+63=128|34|49|99+130=229|exact40|
| Generic width32 |68+63=131|34|49|102+130=232|exact66|
| Generic width784 |74+63=137|34|49|108+130=238|exact1570|
| Complete exact-width Grill |4946+11200=16146|48|3217|4994+11295=16289|at most283247|

In the first three rows, the positive input and positive spread output are supplied parameters, excluded from the49 auxiliaries. In the last row, only the original ordinary positive input is supplied; the encoded queue numeral and recoder output are among the positive witnesses.

## Actual cones and exact equality

The [reviewed native factorization](native_pell_factored_first_coefficient.md) uses

~~~
X=wn2, Y=sn2, E=UM=X*Y, V=ksn2=k*Y,
(E²+X)*V² = L*(L+k), L=E*V.
~~~

Both recoder cores have these literal definitions. Their prefixes are geo__ and and__; inside the composed loader they are rec__geo__ and rec__and__. Each k is its own supplied positive coordinate. Neither k is replaced by the separate computed sum eta+zeta. The independent comparison requiring that equality remains present and cannot be assumed away from a zero.

In each actual cone, the old instructions are

~~~
UM2=E*E,
scaled_norm_coefficient=UM2+X,
ratio_product2=V*V,
L9=scaled_norm_coefficient*ratio_product2.
~~~

The new instructions are

~~~
factored_first_base=E*V,
factored_first_next=factored_first_base+k,
L9=factored_first_base*factored_first_next.
~~~

This replaces3M+1A by2M+1A. Exact expansion gives X²*k²*Y⁴+X*k²*Y² on both sides, using only the paid definitions E=XY and V=kY. It is an identity over every commutative ring, independent of signs, positivity, native typing or any residual equation.

The source checks every defining instruction, each removed register's sole consumer, its absence from comparison operands and its absence from the entire finalizer tail. The existing output name L9 and right operand R9 remain unchanged. In particular, no root convention is imported from the different complete74 source.

The two local identities use distinct proof cuts. After establishing their exact coefficients, the checker uses a shared exact expression interner to prove every common register, every residual and the entire output identical. The finalizer tail is retained literally. The two scopes cannot be accidentally conflated by treating both L9 outputs as one unspecified value.

The history core in the full Grill source has no UM2, scaled_norm_coefficient, ratio_product2 or L9 coefficient cone. It already uses the translated first_unit. Its actual kY multiplier uses its retained computed ratio sum, but the present rewrite never touches it. No third multiplication saving is counted.

## Complete relations and degree scope

All supplied coordinates, domains, comparison lists and source interfaces are unchanged. The recoder's complete ordinary-input theorem therefore transfers directly: for some n>=2 it recodes positive input into spread bits at the fixed width, with both native kernels, repunits, exponent synchronization, congruence and range constraints paid. This standalone relation does not assert canonical n; that is an additional condition of the complete exact-width loader.

For any fixed width b>=4, the existing generic recipe replaces the two private q^4 gates by a chain of mu(b)=floor(log2(b))+popcount(b)-1 products. Its coefficient cones are independent of that chain. The mathematical cost formula becomes126+mu(b) for the comparison certificate and227+mu(b) for its SOS. The guarded executable exposes only the four selected packets in the table; it is not an arbitrary-source or arbitrary-width public optimizer.

The standalone recoder's residual degrees are bounded by max(20,b+1). The first AND norm gives the nonzero degree20 contribution when dominant. For b+1>20, the two repunit rows have nonzero leading terms2^(b-1)*q^b*J and2^b*q^b*K, of degree b+1. Their squares cannot cancel in a real SOS. Thus the displayed exact total degrees are2*max(20,b+1). The full Grill parent's283247 figure is only a syntactic upper bound. The transfer preserves the actual polynomial and this bound; it makes no exact-degree assertion for that form.

The complete Grill form keeps all canonical input-length, denominator-cleared E-value and native-width comparisons. Its input convention is still binary(x+1), least-significant-first. Its unit finalizer remains U*(1+S_H+S_L)-1, with every loader residual inside the positive integer factor. The exact-width proof, positive slack converse and excluded terminal padding are inherited without change.

The actual1,568-phase source table still has all nonhalt productions00 and no source halt. Its role remains a fully emitted fixed-program example. Neither a numerical universal Genera table nor an ordinary-input universal recognizer is added. The literal205-operation example for program011 remains a different table.

## Authentication, executable scope and evidence

The source authenticates eight files: the inline recoder source/receipt, the generic-width recipe, the newly committed native coefficient source/receipt, and all three frozen exact-width artifacts. It reads complete sources from the pinned JSON and does not execute any historical compiler or import SymPy. The long native builder does not run during this delta replay.

The public selected-packet interfaces are canonical_parent, build, rewrite, checked and evaluate. Their variant is exactly one of inline4, generic32, generic784 and exact_width_grill. Full parent/child comparisons are recursive and type-sensitive; fresh packets are rebuilt rather than exposed through a mutable canonical cache. The evaluator requires a complete dictionary of exact positive integers unless an exact signed=True flag explicitly selects integer algebra tests. Fractions are used only by the internal proof checks.

The receipt records exact coefficient and whole-DAG proofs, fully live gate ledgers and unchanged supplied interfaces for all four packets. It also includes full positive/signed/rational evaluations, actual wrong-k counterexamples for both cones, malformed caller rejections and copy isolation. These are checks of the new algebraic transfer, not repeated proofs of the previously reviewed computation semantics or materialized giant Pell zeros.

Replay uses only Python3's standard library:

~~~sh
python3 native_binary_recoder_factored128.py \
  --root /path/to/native-stream-queue \
  --expect native_binary_recoder_factored128.json
~~~

During development, --exact-root may point to the separate directory containing the three frozen exact-width artifacts. After placement beside the other sources, omit it. All required bytes are reauthenticated on each canonical reconstruction; the original packet remains immutable. Use --output PATH to write the deterministic receipt. Optimized Python mode is explicitly rejected.

A concrete next lead is the standalone geometry47 source: its geometry coefficient may admit a separately guarded geometry46 component. This packet does not emit that primitive or claim its complete interface/count; it proves only the two geometry/AND occurrences in these four full sources.

