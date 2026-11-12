# Independent source review: auxiliary-root model bounds

**Source review passes; not elaborated.** The first-ordinate proposal uses
`m>0` before introducing the natural subtraction `q=m−1`, and the existing
IΣ₁ `ArithmeticPellFirstNorm.descent` and `two_le_ordinate` interfaces have
the needed norm and decomposition. Under the explicit `k>2` hypothesis, the
inverse ordinate cannot be zero: its norm would make the inverse first
coordinate 1 and the decomposition would force k=2. The positive inverse
ordinate is at least 2; its norm then makes the inverse first coordinate
larger than `m` times that ordinate. The decomposition gives `k≥8m+4`.

For the other fact-level statements, `c>0`, `i≥1`, `0<Delta<c³` and the
strong norm imply `f²>c+1` by comparing `Delta*c` and `c⁴` without division.
Likewise `c>1`, `i≥1` and `Q=(ic²)²` imply `Q>1`. For the signed gap,
`z²≤1` implies `−1≤z≤1`; hence `0<z+c<f²`. The exact equality
`z+c=f²t`, positivity of f², and `ModelDifferenceRing.one_le_of_pos` force
the ring multiplier t to be at least 1, a contradiction. The multiplier may
be signed; its positivity is derived before discreteness is used.

The checker pins the proposed source and its exact Pell and difference-ring
interfaces, replays the author's source inventory, independently generates
finite Pell solutions using the fundamental-unit recurrence, and checks the
strong-norm and signed-gap bounds on further finite controls. The `k>2`
condition cannot be dropped: the first positive Pell ordinate is k=2.
Those controls do not prove the universal lemmas or elaborate Lean. The
graph-specific scaled-root extraction, k=2 exclusion, `Delta<c³` bound,
signed carrier binding, provider ancestry, graph bridge and iPRA endpoint
remain unproved. No Lean process is run.

From `Computability/DiophantineConsistency`, run:

```
python3 -I -S -B reviews/ordinary14-aux-root-bounds-model-draft-independent/check.py
```

Compare stdout with `result.json`.
