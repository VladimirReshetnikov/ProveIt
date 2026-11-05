# Generic positivity of the free main coordinate

`FreeMainForward.lean` checks three results for the difference ring of each
indicated IΣ₁ model. Given `n≥2`, `c≥3`, `g≥0`, `x<c`, and

```
g² = 1 + (n²−1)*c²,
```

`root_above_base` proves `x+(n−2)*c < g`. With positive `U,H`,
`positive_of_alignment` then proves `h>0` from

```
U*(g−(x+(n−2)*c)) = H*h.
```

`positive_of_pell_bound` replaces the explicit `x<c` assumption with
`x≤n−2` and derives the needed bound using the already checked
`IndependentYBounds.pell_c_bound`. At a 76Y zero, the intended substitution
is `n=a+2`, `x=X`, `h=U*gamma−r`; deriving and composing all of those
hypotheses from the actual graph is **not** part of this packet. The result
does not prove the inverse divisibility, a 72-graph zero equivalence, or an
iPRA endpoint.

The [guarded check](observations/attempt01/result.json) exited 0. Its
[complete log](observations/attempt01/compile.log) reports exactly three
`[propext, Classical.choice, Quot.sound]` axiom lists, without warnings or
`sorryAx`. It used Lean `-M2400`, nice 19, idle I/O, a 120-second wall bound,
and sampled stops at 3.5 GiB process-group RSS and 10 GiB `MemAvailable`.
It recorded 38 RSS samples, sampled maximum 2,111,991,808 bytes, and minimum
available memory 18,530,062,336 bytes; no stop fired. These are sampling
observations, not hard memory reservations. The source, executable and
direct `IndependentYBounds` provider and its companion/shadow guards were
stable before and after. Full transitive source/object, package, dynamic and
search-path ancestry remains inherited.

The runner refuses an existing output directory. To repeat, use a copy with a
fresh output path and coordinate the additional Lean slot; do not overwrite
the retained check.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainForward.lean` | `a276feac4781c3e2436f2d476b80afa0809e7509f645a35c656c8e055a078be2` |
| `check.py` | `2995eb8b6ce0ce6b62c7987f1962a1e4ad55d90bbb8a39e612f2fcbec8aea271` |
| `missing_child.py` | `c5cbe0b2eb1a423889a2865aac23c5714fb2cb5d9feaac2818ce22f7942a29b1` |
| `result.json` | `140647b587bbdf333631a7038ce0e9e51b59520a632b3e916b3befad82100227` |
| `compile.log` | `9856f5be4178a5e1add1d51d0dee999943083067540bfcade114714699d6c793` |
| `/tmp/p64-qcube72-forward-priority-check01/FreeMainForward.olean` | `52e5fd328a5a3e39abfcf7783ce59565524df2ff34c25c6fbe7d330bfb2eb0da` |
