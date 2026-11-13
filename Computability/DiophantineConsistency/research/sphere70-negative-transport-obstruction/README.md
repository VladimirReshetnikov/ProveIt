# Negative transport branch in a proposed 70-operation sphere

A proposed removal of one subtraction gate from the checked 71/80 sphere would replace

```
(P*Q)^2 + (U*W-1)^2 + Z^2 - 2
```

with `(P*Q)^2 + (U*W)^2 + Z^2 - 3`. The latter has the abstract norm tuple `P=Q=U=Z=1, W=-1` as a zero; the former evaluates to 4 there. Thus a proof based only on unit-square extraction leaves an extra `W=-1` branch. The fact that `P`, `Q`, `U`, and `Z` have the required sign exclusions does not itself exclude that branch of `W`.

The transport expression alone permits it even for positive inputs. Let `b=beta*J >= 2`, `q=b+1`, `F=2`, `alpha=b-1`, `z=1`, and take positive `K,w`. Then `C=q-F-alpha=0` and

```
W=(K+w)*C+(q-F)-z*b=-1.
```

`check.py` verifies the last two equalities as sparse polynomial identities over `Z[b,K,w]`, checks the abstract norm example exactly, and checks 3,087 positive finite transport assignments. Reproduce with:

```
python3 -I -S -B Computability/DiophantineConsistency/research/sphere70-negative-transport-obstruction/check.py
```

These are transport-only and abstract-norm checks: no assignment is claimed to satisfy the other full graph equations, and they neither establish a full positive zero nor disprove existential equivalence at the fixed current ports. Excluding the extra branch from the full constraints, or constructing a different fixed-port witness, remains open. No Lean theorem or new graph equivalence is claimed here.

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `c39b53d1b9289bad662ef31840d349d4396300b0479933aeabc2f36403e0e3f0` |
| `result.json` | `bf24a3f515900c3a1370c3003a18edc6d28def92f163edef961751089f26075c` |
