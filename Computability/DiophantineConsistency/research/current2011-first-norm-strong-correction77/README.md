# A 14-variable, 77-operation, degree-64 correction

This is a **source-only current2011 candidate** at the exact fixed ports of
the displayed Carrier65 equation. It has fourteen strictly positive integer
inputs, 77 live integer-leaf binary operations and exact degree 64. The
mathematical argument below gives the same positive zeros as the displayed
equation at the **same coordinates**. A Lean client for this new literal
graph and its internal iPRA endpoint have not been checked.

The [literal graph](graph.json) retains the first 62 rows of the independently
audited [14/72/68 sphere](../fourteen-nonzero-spheres/README.md), including
its current2011 port tuple. The last 15 rows compute the corrected expression
below. The [finite receipt](result.json) authenticates the parent and port
payloads, verifies every row and leaf is live, and checks a fixed-port
degree witness. Its checks complement rather than replace the proof.

## Equation and positive-zero proof

Use the same fourteen positive witnesses and the same `P,Q,W,Z` as the
parent sphere, and its auxiliary factor `U`:

```
P = tau² − ell*(ell+k),             Q = D² − Delta*c²,
W = (K+w)*C + (q−F) − z*(q−1),     Z = f² − Delta*(i*c²)²,
U = Delta*(f²−1)*(V²−y²) + y².
```

All abbreviations are exactly those in the parent graph. Define

```
Zcorr = Z − (i*c)²*(P−1),
equation = (P−1)² + (Q*W−1)² + (U−1)² + (Zcorr−1)² = 0.
```

For an original positive zero, the established
`Carrier65.value_zero_iff_norms` gives `P=Q=W=Z=1`; the established
`ModelCarrierSpheres.auxiliary_of_strong_one` identifies this U with the
original auxiliary factor, so `U=1` too. The correction therefore vanishes
and the new equation is zero.

Conversely a zero of this sum of integer squares gives `P=1`, `Q*W=1`,
`U=1`, and `Zcorr=1`. The correction disappears because `P=1`, hence `Z=1`.
The established negative-unit exclusion gives `Q != −1`. Since Q and W are
integer units with product 1, Q=W=1. Thus all five factors equal 1, and the
original Carrier65 polynomial is zero. The identity map is the witness map
in both directions; no new solvability or consistency claim is made.

## Exact degree

Assign degree 1 to every witness and degree 0 to fixed integer ports. The
parent prefix has `deg E<=6`, `deg Y<=4`, `deg k<=1`, `deg c<=5`,
`deg ell<=11`, `deg H<=6`, `deg tau<=7`, `deg U<=30`, and
`deg (Q*W)<=24`. The apparent degree-34 part of Z cancels. Indeed,
using `a=E+Y`, `c=kY+eta`, and `ell=E*k*Y`,

```
Zcorr = f² − i²*c²*(Delta*c² + P − 1),
Delta*c² + P − 1
  = (a*c−ell)*(a*c+ell) + H*c² + tau² − ell*k − 1,
a*c−ell = E*eta + Y*c.
```

The last expression has degree at most 9, while `a*c+ell` has degree at
most 11. The other displayed terms have degree at most 16, 14 and 12.
Therefore `deg Zcorr<=32`; all four squared deviations have degree at most
64, so this is an upper bound for the full graph.

For the lower bound set all fourteen witnesses equal to an indeterminate t.
The leading part of `a*c−ell` is `k*Y²`; that of `a*c+ell` is `2*E*k*Y`.
The leading part of `Zcorr` is consequently `−2*i²*E*k⁴*Y⁵`, with diagonal
coefficient `−32*beta^19` at `t^32`. All other squared deviations have
degree below 64; the full coefficient at `t^64` is `1024*beta^38`, nonzero
because the actual fixed beta is positive. Thus the specialized degree is
**exactly 64**. The check independently computes the diagonal modulo the
prime 1,000,000,007 using the authenticated whole port values and confirms
this coefficient; the factorized upper bound above is essential.

## Model and provenance boundary

The mathematical identity and sum-of-squares argument extend to the ordered
difference ring of every intended `IΣ₁` model when the assumptions in
[`ModelCarrierSpheres`](../../Lean/DiophantineConsistency/ModelCarrierSpheres.lean)
hold: positive beta and witnesses, `modelFacts`, `negative_unit_exclusions`,
`unit_factors`, `auxiliary_of_strong_one`, and `norms_iff_original`.
The existing checked [fresh-base model/iPRA endpoints](../current2011-spheres-fresh-base/README.md)
cover the earlier 71/80 and 72/68 sphere expressions. They do **not** by
themselves check this new literal AST, an endpoint for it, or a formal
`totalDegree` result. Port-to-PDF semantics and the documented provider
ancestry limits also remain as in those packets.

This profile trades five operations for four degrees relative to the
same-domain 14/72/68 sphere; the latter remains preferable in operation
count. No global minimum or comparison to a different-port graph is claimed.

Run the read-only finite check from the DiophantineConsistency directory:

```
python3 -I -S -B research/current2011-first-norm-strong-correction77/check.py > /tmp/current2011-correction77.json
cmp /tmp/current2011-correction77.json research/current2011-first-norm-strong-correction77/result.json
```

The checker runs no Lean/build process. It verifies source pins, exact
prefix/tail and liveness, four raw/compressed port hashes, and the modular
diagonal calculation. It does not prove the universal inequalities or
perform a proof replay.
