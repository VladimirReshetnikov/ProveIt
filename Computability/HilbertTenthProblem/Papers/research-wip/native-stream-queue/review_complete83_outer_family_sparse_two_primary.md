# Independent review of the sparse-coefficient n>=5 theorem

**PASS; no finding or requested correction.** I read the complete frozen proof and helper inertly, checked the compiler dependencies and every new all-size inequality, and ran only fresh reviewer code. The result establishes the two-primary condition for all permitted outer-family parameters n>=5. Odd-primary completion and n=1 remain open in this packet; it produces no full source zero or universal83 result.

## Authenticated scope

Author stem `/tmp/complete83_outer_family_sparse_two_primary`:

| File | SHA256 |
|---|---|
| `.md` | `bda0275af08ceaf1637b6bfa3ba8a8347205f5a674783cec7105ca263bf3fb97` |
| `.py` | `f68c311277b30f432bb8e89bee66f96601825b8d11c112049f736c070f43f0e2` |
| `.json` | `3c1ec8075c9e6437717b4f1b68a3137b23070c5d5b69ffb080db83f3f17d1e82` |

The reviewer receipt reauthenticates all seven author dependencies. For the new clause census I additionally read the literal `compile_windows` text in complete76's helper lines94--144 and complete78's helper lines162--208, without running or importing either. Complete77 Section1, complete78 Sections1--2, complete76 Section1, and modified75 Section1 provide the proof-level interfaces. The inherited outer-family and corrected digit/carry proofs were previously reviewed in full; this review does not newly certify the whole83 source, its degree, compiler language semantics, or Pell completion.

## Mathematical challenge

The distinction between78's N=m+2 and76/77's **N=m+1** is handled correctly. At least one dummy makes the largest pre-anchor exponent `E0=k+12a+dummy_count−1=N+3a−5`, hence `M=N+6a−4=2w+36a+5+2t`. The mask has exactly `w+9a+3+t` bits and its top parity clause occurs at position `9a+4+t`. Therefore `b>w(9a+4+t)>=26`, giving b>=125. To make the subsequent implication explicit: `2b>36a+16+4t` and `b>2w` together imply `3b>M`. The reserved dummy also gives the used bound `M>=k+15a`.

Each selector has exactly fourteen distinct clause-radix powers: occupancy, nine selected tile copies, and four occupancy/anchor links. Every copy and anchor coefficient has one bit. No multiplication of a selector coefficient by an omitted numerical factor is present. Thus the positive-sum population estimate `pc(K)<=2(14k+9a+4)+6<=30M` follows even if some summands overlap and carry. The lone lowest term is `V^(3a)` with coefficient1: every shifted band, other explicit term, optional correction, and B*DR lies strictly higher. Consequently `v2(K)=3ab`, and odd z preserves that valuation in F.

The subtraction formula is exact: if `T=2^h U`, U odd and `0<c<2^h`, the disjoint blocks of `T−c` are U−1 and `2^h−c`, giving `pc(T−c)=pc(T)−1+h−pc(c−1)`. In particular the three potentially delicate identities in the proof are correct:

```
pc(6F−4)=pc(6F)+v−2,
pc(2F−6)=pc(F)+v−2,
pc(8F−25)=pc(F)+v.
```

For the first deficit, the small correction `4z+2−epsilon` is at least−3. Its negative cases are covered by the same identity, while nonnegative cases use population subadditivity. The resulting common bound `Loss<=5P+3v+log2(d)+6` covers every conservative epsilon in both shapes. Combining product population subadditivity, `pc(z)<=log2(d)+3`, and `M>=15a` gives the displayed bound by `151M log2(d)+456M+3bM/5`.

The uniform estimates are also sound. The derivative used in Section3 is strictly negative: `ln2>1/2` implies `151/ln2<302<456`, already below the constant part of its numerator. Evaluating the decreasing ratio at L=213M and using M<3b is legitimate. The exact base and ratio comparisons prove `log2(639b²)<b/2` for every integer b>=125. The final half-cell comparison reduces simply to `304b>4560`. These are quantified arguments; sampled compiler sizes are unnecessary.

The three high complements consequently lose less than d/2 bits in total. At n>=5, the two or more disjoint low MC cells contribute more than8d/5 bits. Subtracting the unit-bit loss in passing from R to r gives `pc(r)>3D+11d/10−1>3D+1`, as claimed. The previously proved unique-central-term argument then yields the full two-primary divisibility condition. The four-bit shift in the plus shape does not change population or overlap the low and high support ranges.

## Independent finite corroboration

Reviewer stem `/tmp/review_complete83_outer_family_sparse_two_primary`:

| File | SHA256 |
|---|---|
| `.py` | `8963919f700243e9ea6f9a98ae96216c4531e79c2e9628e8ade0bdedc8dcaca2` |
| `.json` | `5538f29c8fb0f01cc77c67b1b476681cb4d27175632c24b9e8558d160caf96b5` |

The fresh checker constructs36 distinct synthetic clause layouts from nine-letter tuples and three padding choices. It checks the coefficient populations, native-position count, radix implications, and unique least term valuation without evaluating an old compiler or materializing K. It separately checks16,400 subtraction identities,13,440 signed deficit cases, and876 integer instances of the logarithmic/rational bounds, alongside their exact base and ratio certificates. The receipt hashes the additional inert source spans.

Writer, normal, and optimized-Python exact receipt runs passed from `/`. The synthetic tuples are not asserted to be allowed machine windows, and their tests are component arithmetic only. Neither the author helper nor any predecessor was executed or imported by this reviewer. No packed R, exponential X, half-binomial Y, Pell witness, or full source zero was materialized by the fresh reviewer. No repository file was changed.
