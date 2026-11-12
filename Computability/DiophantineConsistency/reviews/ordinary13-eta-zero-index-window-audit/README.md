# Source audit: allowing eta=0 in the exact-index argument

The existing proofs of `P72Exact.index_window` and `P72Exact.indices_ordinary` appear to admit **model-natural eta including zero**, while retaining all their other hypotheses. The relevant order replacements use `c=eta+Y*k>=Y*k`, `Y>=2`, and `k>0`; no positivity of eta is needed. This is an argument for a source generalization, not an elaborated Lean theorem or a new graph reduction.

## Every direct eta-positive use

In the pinned `index_window` source, `(hη : 0<η)` is used in exactly three proof steps:

1. `hc0`: it proves `0<c` immediately from eta>0.
2. `hkc`: it obtains strict `k<c` from `k<=k*Y<k*Y+eta`.
3. `hhalf`: it ends `2R<2(R+1)<=2k<=kY<kY+eta=c`.

The call in `indices_ordinary` passes that hypothesis to `index_window`; the only additional direct use there is its `hc2` proof, which currently obtains `2<=c` via a strict `kY<c`. The other uses in `exact_ordinary` and `exact` merely pass eta positivity through to those declarations; they do not by themselves prove the other required hypotheses.

## Noncircular replacements

The early congruence and index data already give positivity before the proof of `c>0` or `n<m`:

```text
R+1 = (2n)%mu <= 2n <= k=2n+4*(X*Y²)*s,
R>=26,  q>=3,  Y=q³*y0 with y0>0.
```

Thus `k>=R+1>=27`, and the existing proof of `Y>=2` uses no eta assumption. Since eta is a model natural, `c=eta+Y*k>=Y*k>=2*k`. Move the proof of `hc0` after the derivation of k>0 and replace the strict estimates by

```text
0 < k < 2k <= Y*k <= c,
2R < 2(R+1) <= 2k <= Y*k <= c,
2 <= 2k <= c.
```

These supply, respectively, `c>0` and `k<c`, the original `2R<c`, and the `2<=c` used to show the signed auxiliary magnitude is nonzero. The strict inequality in the 2R chain already comes from `R<R+1`; the final comparison need only be non-strict. All are finitary ordered-model arguments and work for every eta, including eta=0. The existing main-Pell monotonicity comparison then yields `n<m`; the rest of `indices_ordinary` still needs its main norm, strong norm, signed auxiliary equation and `R+1<mu` premises. In particular, the scalar rank-window theorem's `R>=24` alone does not provide the source's `R>=26` hypothesis.

No circular assumption of the desired eta positivity occurs in these replacements. Conversely, eta=0 and the scale definition alone do **not** imply c>0: eta=k=0 makes c=0. The early congruence plus the k decomposition, or another independent k>0 fact, is essential.

## Boundaries outside these two declarations

This source analysis does not extract any premise from an eta-unshifted graph. Existing 90 graph drafts hard-code `eta=v 9+1`, so their graph norms, gamma/auxiliary clients and valuation maps cannot simply be reused at eta=0. A potential noncircular route, still requiring new graph-bound and Lean-checked clients, is: establish J/b>0 and X,Y>0; get k>0 independently (for example from a still-shifted positive zeta); extract the actual first natural norm and use `ArithmeticPellFirstNorm.two_le_ordinate` to get k>=2; derive the positive-C gap, main orientation and early rank congruence; then use the inequalities above. The cited norm, port, X-forcing and gap adapters must themselves be reproved for the actual unshifted graph and its exact assumptions.

`DirectMainProjection.direct_parts_positive` already takes eta as an arbitrary natural and assumes only U>0, Y>=8 and k>0. `ArithmeticPellPowerRecovery.power_bound` does not assume eta>0, but still explicitly needs zeta>0 and the displayed Pell-coordinate hypotheses. In contrast, the current unelaborated `AuxNormsToBoundsDraft.aux_bounds_of_natural_norms` and its geometry/main-square-gap clients explicitly require eta>0. Their auxiliary-coordinate preconditions need their own generalized proofs or an independently justified route; the index-window weakening does not automatically discharge them. The compact port representation, parent bridge, source/provider ancestry and iPRA endpoint remain separate.

The deterministic checker pins the source snapshots, inventories the four eta-dependent proof uses, and tests bounded consequences of the proposed order chain. Finite controls are not a proof for arbitrary models. No Lean, staging or reduction claim is involved.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-eta-zero-index-window-audit/check.py | cmp - reviews/ordinary13-eta-zero-index-window-audit/result.json
```
