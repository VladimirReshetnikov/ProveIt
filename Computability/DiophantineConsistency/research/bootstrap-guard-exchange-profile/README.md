# Paired coefficient profile for the bootstrap guard exchange

**No improvement in the tested profiles.** The independently reviewed exchange
raw694/base0.T → raw645/shared.Zminus1 preserves integer-zero existence,
but at support caps0,4,8,16,32 it changes neither the output variable count,
quadratic-row count, maximum row support, nor coefficient height in either
family. It adds one expanded quartic monomial in every projected profile
and in the compact unprojected profile. The raw unprojected monomial count
is unchanged. No replacement candidate or frontier improvement is claimed.

## Whole-input comparison

The compact pair starts from the exact901-variable/663-row accepted78-guard
input. The raw pair has all1259 original coordinates/all1177 rows plus78
private triples/guard rows, hence1493 variables and1255 rows. In each pair
all private slots, variable metadata, labels, guard order and source rows
are identical. Only the positive linear guard term changes from raw694 to
raw645 (compact326 to295). Copied census metadata is removed from both
compact inputs; every displayed metric is recomputed from literal rows.

| Family | Support cap | Variables | Quadratic rows | Old terms | New terms | Maximum coefficient |
|---|---:|---:|---:|---:|---:|---:|
| compact78 | 0 | 901 | 663 | 4737 | 4738 | 63905862 |
| compact78 | 4 | 642 | 404 | 5565 | 5566 | 63905891 |
| compact78 | 8 | 616 | 378 | 8582 | 8583 | 2445790974704 |
| compact78 | 16 | 614 | 376 | 8677 | 8678 | 2445790974704 |
| compact78 | 32 | 613 | 375 | 10013 | 10014 | 2445790974704 |
| raw78 | 0 | 1493 | 1255 | 4981 | 4981 | 427 |
| raw78 | 4 | 620 | 382 | 9209 | 9210 | 2445371819760 |
| raw78 | 8 | 613 | 375 | 9661 | 9662 | 2445790974704 |
| raw78 | 16 | 613 | 375 | 9661 | 9662 | 2445790974704 |
| raw78 | 32 | 613 | 375 | 9661 | 9662 | 2445790974704 |

Every polynomial has exact degree4. Variable/row counts and the listed
height agree between old and new in each row. This is a comparison of the
same deterministic optimizer configuration within each family. Different
families can follow different elimination orders; no claim of global
projection optimality follows. In particular, the raw baseline itself
reaches613 variables/375 rows/9661 terms at caps8 and above, whereas the
compact cap32 baseline has10013 terms. That unrelated order-of-projection
difference is not a benefit of exchanging the guard.

## Authentication and verification

`probe.py` reads only immutable JSON sources. It authenticates the whole
archive `docs/incoming/ConZFC_407_888_Quartics_2026-10-24.zip` at SHA256
`59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59`,
and extracts/imports only
`ConZFC_407_888_Quartics/code/integer_pipeline/terminal_elimination.py`,
SHA256 `73ca399b859116cedd9b2b7cb107c82926421697f41ee63b9b61f8bc6c1c0027`.
No source builder, historical emitter, Lean process or inherited generator
is run. Both families use the same `max_support` cap, default affine
support and default affine-first priority.

Each of the20 profiles runs the optimizer’s complete integral substitution
verifier. No unconstrained coordinate is removed. Every deleted coordinate
has a degree-at-most2 integral polynomial restoration, every remaining
row remains quadratic, and all guard rows participate in substitution.
A separate elementary dictionary expansion collects every ordered product
in every complete residual square and compares the entire quartic with the
optimizer expansion. Every unchanged compact metric also matches its
already frozen accepted census exactly. The source hashes are rechecked
after the probe. Normal and optimized-Python receipts must agree except
for their interpreter-mode flag.

`PROFILE.json` and `PROFILE_OPTIMIZED.json` contain complete source pins,
input/output/projection/expanded-polynomial hashes, exact metrics, verified
step counts and restoration-support histograms. They are reproducible
research receipts; full projected equations are deliberately not promoted
or packaged as a new endpoint.

The only changed unprojected residual is v−Aaux with
Aaux=a²+b²+c²+c. Its squared difference is exactly
`(z−T)*(z+T−2*a²−2*b²−2*c²−2*c)`, of degree at most3. This also explains
why the guard exchange alone does not alter the homogeneous quartic part
before subsequent substitutions. The degree4 assertion after substitution
is checked from each entire actual expansion.

## Reproduction and limits

```sh
python -B Computability/DiophantineConsistency/research/bootstrap-guard-exchange-profile/probe.py
python -B -O Computability/DiophantineConsistency/research/bootstrap-guard-exchange-profile/probe.py --output Computability/DiophantineConsistency/research/bootstrap-guard-exchange-profile/PROFILE_OPTIMIZED.json
```

The ordinary exchange is reviewed separately in
`reviews/bootstrap-guard-exchange-peer.md`, pinning proof SHA256
`829b7125dfa1ba9074cc4b93eb247562bebdbc7d7ace0c4edf2b7c1981b8fff3`.
This profile is finite exact arithmetic, not an internal-ZFC proof or Lean
formalization. It establishes no improvement outside these ten paired
configurations and gives no reason to replace an accepted equation.
