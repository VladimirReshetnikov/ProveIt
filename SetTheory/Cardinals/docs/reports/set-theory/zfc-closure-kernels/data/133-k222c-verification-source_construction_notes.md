# Source construction for the combined 222-state candidate

## Exact inputs and output

The construction uses the witness-request package `K223_Construction_2026-10-20 (3).zip` as its semantic source parent. Its source digest is `df55079f114a6aa9ada970d7d857726e47e3a3dba2a721245ebbacfd4577c13c`, and its K-labelled table digest is `7e036b1bd05fe8a7e5877a8c5386cae603f4d689adeeb13754ee98dca998bfef`. Macro contracts are reconstructed from the pinned K224 package embedded in that parent, using its exact Dag230 source. The equality/helper transformation is the independent G construction in the other delivered K223 package. The final optimized source digest is `cc1fbb3a16dd446af9c7cdb678317d31060082e6794b9c7074ce02b46584a75e`.

The authoritative new script is `build_combined_source.py`. It accepts `--seed-root`, `--baseline224`, and `--output`. It pins both parents, derives the new source without reading a stored candidate source as input, and emits an exact source plus a receipt. The separate binary compiler should use the G223 table as its table parent: its shared decoder contexts already accommodate the altered equality row. This choice affects machine compilation, not the numerical calculus defined by the source.

## The two emitter changes

Write I, R, Q, and E for the four numerical constructors and N(x)=I(x,1). They are arithmetic constructor functions on every natural number, including numbers that are not orthodox first-order formulas.

The numerical equality row changes from

`I(E(c,a), I(E(c,b), E(a,b)))`

to

`I(E(c,a), I(E(c,b), Q(R(a,b), E(a,b))))`.

This is exactly G with binder RelCode(a,b). The old row occupies primitive interval [486,786) in the seed source and has 300 instructions. Its replacement has 409 instructions. The actual edit preserves the useful old factors in the two antecedents: at the smaller interval [648,732), replace the closed sequence `(pair_inc, Eq(a,b))` by `((pair_inc,(Rel(a,b),Eq(a,b))),All)`. Re-emitting the full numerical row from scratch would unnecessarily discard inherited source sharing.

Let V be membership vacuity, E_h the restricted equality helper, W the repeated witness request, and H the hereditary support-and-closure expression. The old seed bundle is

`T = Q(c,I(H,N(W)))`,

`B = N(I(V,I(E_h,T)))`.

The new bundle is

`B' = N(I(V,T))`.

It keeps the actual K_s core, its variable labels, both copies of W, the numerical private code, and the membership-vacuity implication. Only the separately emitted equality helper and its enclosing implication disappear. The old bundle occupies primitive interval [2541,4781) and has 2240 instructions. The new 65-macro word has 1913 instructions. The script compares symbolic arithmetic expression trees, so the emitter claim holds for all natural a,b,c and does not rely on numerical sampling.

Thus the complete primitive census is

4962 + (409-300) + (1913-2240) = 4744.

All primitive instructions outside the two stated intervals are unchanged. In particular the eight logical-row positions, the gate `c=a or c=b`, the enumerator, the proof cutoff, and the contradiction code1 retain their parent interfaces.

## Source structure and the reset bound

Pruning the helper and inserting G directly into the seed's exact binary source tree initially gives 208 distinct subtrees, 4744 leaves, maximum depth36, and one address containing seven consecutive zero bits. That address is `11101001001110000000` and selects `CI 1`.

The inherited reset routine requires maximum zero run at most6. This condition is material: a prior G source with a seven-zero address failed the unbounded runtime checker. The new construction therefore performs the closed right rotation at source address `1110100100111000`:

`((P,Q),R) -> (P,(Q,R))`.

All three factors have boundary `(0,0,False)`. The script applies the rotation to the selected subtree wherever it occurs. It preserves the entire primitive instruction word and every guarded control-flow edge. The final source still has208 distinct subtrees and4744 leaves, while its maximum zero run becomes6; maximum depth remains36.

## Independent source/emitter certificate

The builder replays nine local all-register macro bisimulations against the pinned Dag230 programs. These cover the variable pushes, literal1, the four arithmetic constructors, and negation. Their intended interface is arbitrary previous top and older stack, with the inherited clean scratch registers. It then symbolically evaluates both old and new row words and both old and new bundle words, and compares the entire final primitive word with the explicit two-interval replacement in the old source.

A second source is built independently at the smallest closed ancestor containing all the edits, address `11101001001110`. This reference consists of15 closed factors: the direct G insertion and retained closed chunks from the old source. It does not use the optimized source's new parenthesization. Both the arithmetic and interval control-flow resolvers show that this reference, the unrotated combined source, and the final rotated source have identical guarded control-flow graphs, each with6167 resolver cases. These are source control-flow cases; the binary runtime checker has its own census and includes the halt boundary separately.

The source certificate establishes the numerical emitter and register-program structure. The native calculus comparison and complete binary execution remain distinct obligations. The proof-audit agent's seed-order bundle certificate supplies the exact propositional roots `B -> B'`, `B -> E_h`, and `B' -> (E_h -> B)`. Together with the inherited G derivations they prove literal equality of the combined and seed native theorem sets. The seed theory's comparison with ZFC is an equiconsistency translation, not a theorem-set equality with the output-root K theory.

## Limited alternative measurement

One extra binder variant was measured: replace G's RelCode(a,b) binder by EqCode(a,b), using the already present closed Eq(a,b) macro twice. The resulting source has208 subtrees and4746 instructions, but zero run7. It provides no source-DAG saving and was not compiled or promoted. This is one explicit measurement, not a lower bound on other binder encodings or grammars. Its exact record is `alternative_measurement.json`.
