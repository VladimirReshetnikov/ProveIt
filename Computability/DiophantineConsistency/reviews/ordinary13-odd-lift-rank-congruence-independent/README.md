# Independent review of the odd-index rank counterexample

The pinned fact-level example has a valid positive strong witness and a positive square-auxiliary completion while the earlier scalar sufficient condition fails. The sign correlation and exact modular congruences check out. It does not establish a graph zero: its `A=2` is impossible for the actual shifted graph, and its rank is a chosen integer rather than a graph-derived value.

The exact recurrences give the main pair `(26,15)` at `A=2,m=3`, and the strong pair `(f,v)=(189750626,109552575)` at index 15. With `I=3v=328657725` and `i=1460701`, both `I=15²*i` and `I²=3*(f²-1)` hold; also `f²≡1 mod 15`. The proposed rank `R=12` fails the sufficient condition because `15` does not divide `R-m=9`.

For the stated odd auxiliary index `ell=218943027`, the independent checker verifies `ell≡3 mod 4`, `ell≡R mod 15`, and `y_ell(2)≡15 mod f²` by modular matrix powering. Taking the positive auxiliary first coordinate corresponds to `epsilon=+1`; with `j=(ell-1)/2` odd, the shared sign is `sigma=epsilon*(-1)^j=-1`. Thus both correlated congruences hold with that same sign.

The original checker computes `W=x_ell(I)/I` through its integer quotient-polynomial recurrence. This review checks W by a different exact method: compute `x_ell(I)` modulo `I*f²*c`. Because ell is odd, the actual integer coordinate is divisible by I; the modulus is also divisible by I, so its canonical remainder is divisible by I. **Exact integer division of that remainder**, rather than division by a modular nonunit, gives `W mod (f²*c)`. The result satisfies `W≡-15 mod f²` and `W≡3 mod 15`. It follows that `(W+15+12f²)/(15f²)` is an integer; it is positive because `W`, c and R are positive. The Pell norm then gives the actual square-auxiliary factor one. Neither enormous Pell coordinate needs to be expanded.

The pinned parent rows identify the literal strong and auxiliary fields and give `A=Y*(X+1)+2`, where natural inputs and shifted `s` imply `Y=q³s≥1` and `X≥0`. Hence the actual graph has `A≥3`, so this example cannot itself be a graph witness. Its exact modular identities remain useful as a counterexample to deriving the scalar condition from the two correlated congruences in the abstract Pell setting.

The review checker pins the source packet and graph, verifies the small exact norms and both signs' convention, performs the independent modulus-and-exact-division computation above, and checks the graph's A bound. These checks do not establish TeX, Lean, arbitrary-model, provider, or iPRA semantics.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-odd-lift-rank-congruence-independent/check.py | cmp - reviews/ordinary13-odd-lift-rank-congruence-independent/receipt.json
```

No Lean, build, staging, or huge auxiliary coordinate was produced.
