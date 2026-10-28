# Fourteen positive variables: 71/80 and72/68 nonzero spheres

The two complete equations are

```text
(P*Q)^2 + (U*W-1)^2 + Z^2 - 2 = 0,
P^2 + U^2 + Z^2 + (Q*W-1)^2 - 3 = 0.
```

Here every abbreviation is defined in [PROOF.md](PROOF.md), with the exact
fourteen-coordinate Carrier65 order and current2011 fixed integer ports.
The complete operation arrays are [polynomial71.json](polynomial71.json)
and [polynomial72.json](polynomial72.json). The entire positive zero sets
are preserved by identity maps; these are not polynomial identities with
the earlier product equation. In particular the independent coordinate
`y>0` is retained, the strong norm uses `i` rather than `beta*J*i`, and
`MF_source` already contains its single beta shift.

| Positive variables | Binary operations | Multiplications | Additions | Subtractions | Exact degree |
| --- | --- | --- | --- | --- | --- |
| 14 | 71 | 39 | 18 | 14 | 80 |
| 14 | 72 | 39 | 19 | 14 | 68 |

Both use all fourteen coordinates and four fixed ports. The coefficient
copies in [coefficients](coefficients) are the complete current2011 tuple,
47313 raw bytes, byte-identical to the accepted65-operation parent. The
historical66/118 finite tuple used2501 ports and is not used as coefficient
data here. These two tradeoffs are mutually incomparable, and trade an
additional variable for lower operation count and degree relative to the
13/75/96 sphere. No global minimum is claimed; the maintained page is
unchanged.

## Proof and finite audit

[NearSquareNormZero.lean](../../Lean/DiophantineConsistency/NearSquareNormZero.lean)
proves the integer descent excluding a zero norm with coefficient `A^2-1`
when `A>=2` and the second coordinate is nonzero. It has no native machine
or consistency prerequisite.
[CarrierNonzeroSpheres.lean](../../Lean/DiophantineConsistency/CarrierNonzeroSpheres.lean)
uses that lemma for unconditional nonvanishing of P,Q,Z,U. The f=1 case
for U uses positive y; the f>=2 case uses an exact transformed norm. The
negative-unit exclusion for U is used only after Z=1. Both whole positive
zero-set equivalences then compose with the actual current-port external
Lean ConZFC endpoint. No internal HA, PA or ZFC derivation follows from
these external equivalences.

The independent standard-library [auditor](audit.py) imports no project
code. It binds the exact51-row parent prefix and both complete replacements,
checks every binary operation and dependency, derives every gate's complete
homogeneous leader (including the full323-term main-norm cancellation), and
reconstructs all four current ports from the pinned native coefficient
array. It separately checks full formal graph identities, selected nonzero
specialized coefficients, actual-variable and port dependence, and mutation
controls. Bounded square diagnostics do not replace the unbounded Lean
proof. Exact-degree claims belong to this finite audit, not a new Lean
`totalDegree` theorem.

Read-only reproduction, from the repository root:

```sh
python3 Computability/DiophantineConsistency/research/fourteen-nonzero-spheres/audit.py
python3 -O Computability/DiophantineConsistency/research/fourteen-nonzero-spheres/audit.py
```

The `--write` option materializes only this packet's graphs, coefficient
copies and certificate; the default runs require exact deterministic bytes.
All guards use explicit exceptions and remain active under Python `-O`.

Validation: both generic Lean leaves and both actual-carrier leaves passed
fresh capped builds. The eleven carrier axiom reports and one generic report
contain only `propext`, `Classical.choice`, and `Quot.sound`. The actual
carrier leaves used the current merged native cache with exact source/object
pins, not the historical native snapshot. Both finite read-only runs (normal
Python and `-O`) reproduce the complete certificate after materialization.
See the [author receipt](../../reviews/fourteen-nonzero-spheres-author.md)
for exact source/object/log hashes, the retained first alias-rewrite failure,
cache provenance and precise validation limits. Independent acceptance is a
separate review step; none is implied by this author receipt.
