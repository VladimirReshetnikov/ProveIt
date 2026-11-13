# Binding the symbolic compact tuple to the retained 95-row candidate

The [four-port Lean theorem](../compact44-four-port-byte-assembly2/README.md)
now proves that four closed Lean byte recipes decode to the symbolic tuple;
the [model client](../compact44-byte-ports-model-iff-prototype/README.md)
uses them in the shifted 95-gate expression. This is not a Lean theorem
about external files. The supplement's formerly missing coefficient copies
and other manifest entries have been [restored and externally verified](../supplement-pinned-restoration/README.md)
against the exact pinned parent bytes. JSON/Lean source transcription,
filesystem and gzip correspondence, PDF transcription and an iPRA endpoint
remain separate obligations. The earlier plan below is retained as history.

The checked all-model iff uses the symbolic tuple

`[CompactFixedBeta.betaNat, paramKernel rho, lowNat, betaNat + highNat]`

from `CompactSymbolicPorts`, with `rho=2^67`, `betaNat=2^590069−1`, and the high shift applied exactly once. `CompactSymbolicPorts.lean` is pinned at SHA-256 `0c2f2859c5420b3d22b73c3e5e72a7307a75d2b83d95d29eb7691f085d812148`. The intended 95-operation graph is `con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive12_95_degree70.json`, SHA-256 `2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22`. The similarly named `candidates/free-j-polarized-positive/equation.json` has **96**, not 95, rows; it is a parent and source of the retained coefficient package, not the exact 95-row graph.

The four target payload files are in `candidates/free-j-polarized-positive/source/positive/coefficients/payloads/`, with unsigned minimal little-endian interpretation specified by its `BINDING.json` (SHA-256 `dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01`). In order, the decompressed bytes are `beta.bin.gz`, `K.bin.gz`, `MC.bin.gz`, and **already shifted** `MF_source.bin.gz`. Their recorded raw SHA-256 values are respectively `0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d`, `c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e`, `6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4`, and `48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737`. The alternate BFS K has a different raw hash and is not this target. The manuscript supplement's missing copies have now been restored from manifest-matching parent files; their file identity remains an external provenance check, not a Lean theorem about gzip.

## Earlier proposed Lean endpoint (historical)

The following records the initial approach; the checked implementation uses
closed natural-digit recipes rather than the proposed `Fin 256` literals.
The [assembled tuple theorem](../compact44-four-port-byte-assembly2/README.md)
and its [model-level client](../compact44-byte-ports-model-iff-prototype/README.md)
have since been checked with author-side provider qualifications.

Introduce four *separately named, source-pinned Lean byte literals* `Bβ`, `BK`, `BMC`, `BMF`, each a list of `Fin 256`, generated from the decompressed intended payloads and partitioned into bounded chunks. Define `decode bs := Nat.ofDigits 256 (bs.map Fin.val)`. Prove the four standard-natural equalities, without expanding the large integers as numerals:

```
decode Bβ  = CompactFixedBeta.betaNat
decode BK  = paramKernel rho
decode BMC = lowNat
decode BMF = CompactFixedBeta.betaNat + highNat
```

The final equation is **not** `decode BMF = highNat` and must not add another beta. These equalities can be joined pointwise into `retainedPorts = ports betaNat (paramKernel rho) lowNat highNat`, then lifted through integer casts and through `Ordinary12FreeJ.literal` by function extensionality and congruence. Use the actual source order `beta,K0,MC,MF`; avoid a large closed `decide`, expanding the `Nat` values, or changing an already checked symbolic model theorem's port tuple.

The separate 95-row syntax obligation is an exact Lean equality between a source-pinned retained row-program interpretation and `Ordinary12FreeJ.literal p` for arbitrary `p`; then specialize the four ports by the above equalities. The existing `free-j-prototype/check_graph.py` checks the 95 rows, variable order and arbitrary port slots externally, but is not a Lean theorem about the JSON. A [direct generated expression](../free-j-retained-direct-expression-prototype/README.md) now has an author-checked Lean equality for arbitrary ports; its JSON-to-source generation remains external. The separate array-interpreter equality did not complete at its resource bounds. The iPRA adapter concerns `positiveShift (literal p)` over unrestricted naturals; retain the distinction from the original 95-row positive-variable graph when forming the final statement.

## Earlier proof plan and materials (historical)

The K, MC and MF bullet points describe work proposed before the subsequent
checked closed-recipe reconstructions and tuple assembly linked above; they
are not a current list of unfinished symbolic Lean equalities.

1. **Beta:** an [author-checked byte-recipe theorem](../compact44-retained-beta-byte-prototype/README.md) now proves that decoding 73,758 base-256 digits of 255 followed by 31 equals symbolic beta, without evaluating the 590,069-bit numeral. A separately pinned external check matches that recipe to the retained parent gzip payload; the Lean theorem itself does not establish the filesystem or gzip correspondence.
2. **K:** `SymbolicKernelBytes.kernel_byte` gives each little-endian byte of the sparse radix-`2^67` kernel through two neighboring radix digits; source SHA-256 `b245515e66a89eba3be43d5edb96197d55c7a5138095c429f21ea920d63761b2`. `TopDigitClean`, `LastByte`, and `MiddleGap` give the exact top bound and symbolic zero intervals; `LastByte.lean` and `MiddleGap.lean` are pinned at `7ef8c2e02b889fc0268bffd7018167285012298ba328ecd4c9f0583c3ed1e309` and `81075154600d32850b9d6a1d6b1bb7ac565d4e65ccc39f70b3ecad8f2e3b8c60`. Their two gaps plus the last byte cover 37,253 of 74,111 byte positions **symbolically**, leaving 36,858 positions for finite certificates; they are not yet Lean equalities to file bytes. Prove the remaining byte-window equalities in bounded chunks, include the already known gaps, and prove a generic byte-extensionality/reconstruction theorem to obtain `decode BK = paramKernel rho`. The earlier external K byte comparison is evidence, not a Lean equality.
3. **MC:** `CompactConcreteIncrement.mask_eq_bit_recipe` provides the sparse complement-sum formula, and `CompactSymbolicMaskCasts.low_cast` identifies its model alias. The latter is not a byte equality. Reuse a generic radix-window/byte reconstruction theorem and prove bounded chunks for the actual `BMC`; exploit repeated all-one or zero runs symbolically where available.
4. **MF:** `CompactHighPopulation.highDigits` is an explicit 8,807-digit sparse/run-length recipe, and the actual fixed port is `betaNat + Nat.ofDigits (2^67) highDigits`. Prove byte windows for that *sum*, including carries and the extra bit at position 590069, then certify the actual `BMF`. Do not infer bytewise addition or no-carry without proof. `CompactSymbolicMaskCasts.high_cast` is an alias theorem only.

The initial window and suffix sources alone did not establish the tuple.
The later tuple theorem does prove the four recipe-decoding equalities in
Lean, subject to its provider qualifications; it does not establish that
external gzip streams decompress to those recipes. A digest comparison,
Python reimplementation, `native_decide`, or a generated literal alone does
not prove a Lean file equality.

## Trust and serialization boundary

Lean equality to `decode BK` proves a fact about the literal list, not that the filesystem's gzip decompresses to it. Either formalize the retained compressed bytes and a verified gzip decoder and prove its output is the literal, or explicitly retain a pinned external file/decompression-to-literal check as a provenance assumption. Likewise, the `equation.json`-to-Lean row transcription needs a verified parser or a clearly stated external source pin/check. A PDF or other displayed equation needs its own exact transcription and coefficient binding; the 14-variable `equation.pdf` is a different target from this 12-variable 95-row candidate.
