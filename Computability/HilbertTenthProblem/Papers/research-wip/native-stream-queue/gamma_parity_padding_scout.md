# Harmless parity padding of the actual native window compiler

The parity required by the new native prime filter is attainable for every c.e. language through a finite, input-independent change to the **actual window-list compiler**. It does not require a claim that an abstract machine can be padded to have a prescribed number of local windows.

The operation below preserves exactly the old Start-containing cyclic overlap words and their marker distances. It produces an even number of selectors and an odd tile-alphabet size. It changes the fixed compiler numerals, so it does not remove the hypothesis for a previously fixed coefficient instance. No arithmetic circuit or new operation bound is produced in this scout.

## 1. The concrete accepted interface

The current modified compiler calls `baseline.compile_windows(windows, alphabet_size)` in [complete75_half_binomial_compiler.py](complete75_half_binomial_compiler.py), lines 21–40. The baseline is [explore_fixed_raw_universal_76.py](../../verification/explore_fixed_raw_universal_76.py), whose literal function at lines 94–148:

* converts the input to an ordered tuple of ordered tuples;
* requires at least two windows, pairwise distinct, each of length nine;
* requires every symbol to lie in `range(a)`;
* assigns selector indices `0,...,k-1` without renumbering the supplied order;
* creates copy bits for all nine positions and every symbol in `range(a)`;
* ensures at least one ignored dummy position, then chooses the separated anchors, bands and powers-of-five parameters from this finite data.

There is **no requirement that every symbol occur in a window**, nor a guard requiring a particular machine-generated window list. Distinctness rules out simply repeating an old window to alter the parity; the construction below adds a genuinely new one when needed. The modified wrapper strengthens the radix bound, selects the first ignored dummy, and exports its changed masks. Its interface does not impose a further alphabet-use restriction.

These are source inspections, not executions of either historical module. Their imports, self-tests and builder functions were not run.

## 2. The explicit padding

Let the original tile alphabet be A={0,...,a-1}. Let the ordered, distinct allowed windows be

```
W=(w0,...,w_(k-1)), k>=2,
w0=Start, w1=End,
wi in A^9.
```

These are the marker indices of the current 77/76/75 compiler, not the reversed indices in the older 80/78 presentations.

Choose the least odd a' strictly larger than a:

```
a'=a+1 if a is even, and a'=a+2 if a is odd.
```

Let star=a be a fresh symbol and J=(star,star,...,star) the nine-entry uniform window. Define

```
W'=W                  if k is even,
W'=W followed by J    if k is odd.
```

Then a' is odd and k'=|W'| is even. The ordered old entries and especially indices 0 and 1 are unchanged. Every window lies in {0,...,a'-1}^9. When J is added, it is distinct from every old window because no old symbol equals star. If an additional alphabet symbol was added, it is unused. All the literal API guards are satisfied.

The padded relation may admit new **unmarked** words, such as an all-J word. The claim is preservation of the Start-containing relation required by the compiler, not equality of the unmarked window languages.

## 3. Exact marked-language preservation

The generic center clauses force each cell to have either one selected window and its exact tile-copy indicators, or no selector and all tile-copy indicators zero. See [the native copy proof](../../1980/FIXED_RAW_UNIVERSAL_80_PROOF.md), lines 47–73. This argument applies to any distinct finite list of nine-tuples and does not require all alphabet symbols to be used. In an old selected window all new-symbol copy bits are therefore zero.

The decoded horizontal relation is the literal six-position overlap

```
center[row,col+1]=right[row,col],
row=0,1,2 and col=0,1.
```

The occupied Start cell propagates occupancy through this horizontal relation to every cyclic cell: an occupied window has exactly one indicator at each physical position, while an empty cell has none, so equality of the overlap indicators excludes an occupied/empty boundary. The horizontal offset is one, which is one orbit on Z/NZ, including the wrap-around edge. The source proof states this explicitly at lines 237–244 of the same native copy proof. In the current marker convention, [the 77 proof](../../1980/FIXED_RAW_UNIVERSAL_77_PROOF.md), lines 176–198, first recovers the full origin Start, then the anchors/alignment and both overlaps; it does not require prior uniqueness of Start.

Now assume J was added. An old window and J cannot overlap horizontally in either direction: every entry of each shared position would have to belong both to A and to {star}, two disjoint alphabets. Thus the indicator “this occupied cell selects J” is constant along horizontal adjacency. The origin selects old Start, so the indicator is zero there and hence zero at every cell of the ring.

It follows that every decoded Start-containing W' word uses only W. Its horizontal and vertical overlap relations, Start and End occurrences, length N and temporal stride h are exactly those of the old word. Only after excluding J do we invoke the inherited old-machine helical theorem or cyclic marker bijection. In particular no semantics of an artificial J state is presumed.

Conversely every old marked cyclic overlap word is a W' word: keep its selected old windows, put all new-symbol copy indicators to zero, and use the same marker positions and overlaps. The additional all-J selector, if present, is zero everywhere. The construction is independent of the temporal stride: neither occupancy propagation nor exclusion of J assumes h divides N. Horizontal shift one supplies the necessary connectivity even when the temporal permutation has several orbits.

Therefore, for every N and h for which the old marked word is defined, the allowed marked window sequences are exactly the same, under the literal inclusion of the old list in the new list. This proof covers multiple potential Starts before the original marker-bijection theorem establishes uniqueness; the presence of the origin Start already excludes J.

## 4. Ordinary input and fresh completeness at new numerals

The 76 construction uses a fixed machine for S_even={2x:x in S}, with Start at the last I of its initialization run and End at the first. See [its fixed-machine interface](../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md), lines 18–37. The current source places End at **cell distance 2x**, using the exponent `2*d*x+b`. The padding above does not alter the machine, its old windows, the indices Start=0/End=1, or that cell distance. For the newly compiled b',d', the same source formula is `2*d'*x+b'`; its unit End-selector offset is b', and its whole-cell offset is still 2x. The ordinary external input x is unchanged.

The new fixed layout will generally have different b',d',B', masks and clause numerals. They are computed from W',a' once for the chosen semidecider and do not depend on x. The wrapper still provides an ignored dummy, the optional high correction, and powers-of-five b',L',d'. Unused symbols contribute legitimate copy positions and clauses, whose indicators are zero on the old histories; this does not invalidate the generic coefficient bounds or the anchor construction.

For completeness, choose fresh sufficiently large spatial and temporal powers-of-five padding for the old accepting computation, after the new fixed numerals have been computed. The retained helical theorem permits independent sufficiently large width and height. Thus all new requirements, such as N>25d', N>2x, adequate spatial h, and the later finite switch-grid bound can be met. Lift the old marked window word as in Section 3, apply the new compiler's dummy alignment, and use its inherited kernel/positive-witness converse. This is a fresh witness construction with new coefficient numerals, not a numerical map preserving an old Pell tuple.

For soundness, the new source's generic typing, occupancy and overlap arguments recover a marked W' word. Section 3 removes J before applying the old accepting-run semantics. Accordingly the compiler-level ordinary-input language is unchanged in both directions.

The current effective exporter chooses the first dummy. With a' odd and k' even, the exact table in [the compiler-order filters](complete75_gamma87_compiler_order_filters.md), lines 40–103, gives MC=0 modulo 3 and hence R=0 modulo 3 on canonical odd-N histories. This is precisely the parity class required by [the new small-prime theorem](complete83_gamma_small_prime_digit_rules.md). Its genuine-history filter can therefore be arranged for a representation of **every** c.e. language by choosing this padded recipe. The frozen theorem remains conditional for an already specified coefficient instance; this separate padding result supplies the condition for a newly compiled representation.

This conclusion does not prove or refute the language of the independent-gamma83 chart. The prime filter leaves the rest of its alias modulus uncontrolled. The scout neither emits new compiler numerals nor claims a new paid arithmetic count.

## 5. Read scope and authenticated data

This was a bounded source/proof read. The relevant source spans were read inertly: `explore_fixed_raw_universal_76.py` lines 94–166; `complete75_half_binomial_compiler.py` lines 1–90; the older 77 compiler lines 68–129 for the inherited selector/layout correspondence. Proof spans were: 80 lines 25–73 and 229–264; 78 lines 25–120; 77 lines 176–214; 76 lines 18–37 and 155–211; modified75 sections 1, 4–6; and compiler-order-filter sections 1–2. No predecessor Python, archived code, verifier, builder, Lean build or repository edit was performed. The proof is parametric in the finite list; no universal window list or complete positive Pell tuple was materialized.

The files directly supporting the conclusion have these SHA256 hashes (paths below are relative to `Computability/HilbertTenthProblem/Papers`):

```
verification/explore_fixed_raw_universal_76.py
011097aaee5acb02e938e66f8e6adcec711cf5a097d87a9f50a3cf28f19d97d0
research-wip/native-stream-queue/complete75_half_binomial_compiler.py
d6bed0afef319e5a702bda6b9959bf3888e101da7879b77953c345182f8032d2
1980/FIXED_RAW_UNIVERSAL_80_PROOF.md
655128efc0b03d44cd9ba0ba62857ae888e7a583371a40ae3861d4fd521a1076
1980/FIXED_RAW_UNIVERSAL_78_PROOF.md
b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39
1980/FIXED_RAW_UNIVERSAL_77_PROOF.md
292acdfe5ff598201c3dd9cd7defff07b45d743637c1f3836a21065888053a41
1980/FIXED_RAW_UNIVERSAL_76_PROOF.md
75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87
research-wip/native-stream-queue/complete75_half_binomial_compiler.md
68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117
research-wip/native-stream-queue/complete75_gamma87_compiler_order_filters.md
43d613204d6dc7192763e87e120f84ea0e3f18849a4fd23be26f56ca45b9fcc3
```

The referenced revised small-prime note is pinned separately by SHA256 `b7248efe5f292bd5dcbf093ccd9f664d663b2eb23c022974b1a9f64b537a4f8e`; it is unchanged by this scout.
