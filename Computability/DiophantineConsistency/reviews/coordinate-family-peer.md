# Peer review: shared-certificate integer coordinate family

Status: **PASS for the new ordinary polynomial reductions and finite construction.**
The three packets define fixed equations over unrestricted integers. Their
new maps preserve the complete integer zero sets of the authenticated
25-variable octic, with no additional sign, divisibility, or nonzero premise.
This review does not provide a new native compiler calibration or an
internally encoded object-ZFC derivation. Lean work remains paused.

| Packet | Integer variables | Residuals | Exact degree | Expanded residual terms |
|---|---:|---:|---:|---:|
| `coordinate21_degree16.json` | 21 | 9 | 16 | 1,026 |
| `coordinate20_degree18.json` | 20 | 8 | 18 | 1,035 |
| `coordinate19_degree40.json` | 19 | 7 | 40 | 6,653 |

The 20-variable degree-18 equation improves the previously reviewed
20-variable degree-20 point. The 19-variable degree-40 packet improves its
named degree-88 predecessor but is dominated in variables and degree by the
already reviewed 19-variable degree-28 point. No circuit-operation frontier
claim is made: these packets supply expanded residuals rather than an
optimized literal arithmetic DAG.

## Authenticated input and coherent coefficients

The incoming archive is `ConZFC_Shared_Certificates_2026-10-24.zip` from
commit `751bc067e2`, SHA256
`61582dab90e880049e61ff1a5c49386747cd063de15e18411a20f327b9559ba1`.
The independent checker compares all 59 coordinate-family members with the
original ZIP and all 23 retained source files with their actual repository
contents at commit `08200eb10fde2db408c69dffd840d6920a569b1f`.
It also authenticates the original joint-guards ZIP and its literal
`joint25_octic.json`, rather than accepting the new package's baseline as
an unverified source.

The complete source-34 `mixed-parity-unrounded-1064921` tuple is retained:
`beta = 2^1064921 - 1`, the original `K0, MC, MF`, and determinant scales
`cone_A = 2^1113`, `cone_B = 2^666104`. Their six minimal unsigned
payloads total 615,883 bytes. Every raw hash, size, bit length, literal
power, and mask inequality was checked. The native `MF` is already shifted
and is used once. No compact54 coefficient or individual port is substituted.
The supplied finite source-34 constructor independently reconstructs the
same four native integers in both replay modes, including its 69,230 basis
convolution checks.

## Universal map argument

First permute the incoming 13 rows by
`[0,1,2,3,4,5,6,7,11,8,9,10,12]`. Keep the pivot, original row 11,
unchanged. Adding respectively `(E-a)`, `-E(c-eta)`, and `1` times
that pivot to rows 2, 3, and 5 gives the reconstructed baseline exactly.
All 13 identities hold over the integer polynomial ring. The inverse
subtracts those multiples and reverses the permutation, so this step
preserves simultaneous vanishing without a field or sign assumption.

For 21 variables, make the triangular coordinate changes

```
C = q-F-alpha,  Y = a-E,  k = eta+zeta,
s = tau-E(c-eta).
```

Their polynomial inverses are
`alpha=q-F-C`, `a=E+Y`, `zeta=k-eta`,
`tau=s+E(c-eta)`. The checker verifies both compositions before imposing
any equation. Four baseline rows then restore the deleted coordinates

```
F = (K0+W)C-z(q-1),  E = WqY,
eta = c-Yk,          V = fo-c.
```

These right sides contain none of the four deleted coordinates. They are
integer polynomials on every retained tuple. Their defining rows become
identically zero; all nine retained source rows become the delivered nine
rows exactly. Projection and restoration are therefore inverse on zero
sets, including tuples with zero or negative `q,C,Y,k,c`.
The norm shift uses the exact identity

```
(s+u)^2-(k+u)^2+(k+u)k-1 = s^2+(2s-k)u-1,
u = EYk.
```

For 20 variables, replace the unrestricted old root `y` by `fo+b` and
delete `I` through its monic definition `I=(2r+1)c^2`.
The root change has inverse `b=y-fo`; it requires no size or sign bound.
The identity

```
(fo+b)^2-(fo-c)^2 = (c+b)(2fo+b-c)
```

reduces the auxiliary residual to degree nine. All eight restored rows
match the delivered packet. For 19 variables, delete the monic first row
through `Y=(2v+1)q^3`. The seven remaining rows again match exactly.
Across the three stages the independent checker verifies all six deleted
rows and all 24 retained-row identities, not a selected subset of equations.

The inherited signed-Pell and determinant proof applies to the same whole
source tuple as before. None of these new changes selects positive signs.
The earlier source-34-to-octic construction is an inherited existential
calibration; the new maps from the octic onward are the polynomial zero-set
bijections reviewed here. These two scopes should remain distinct.

## Exact degrees after fixing the coefficients

The independent residual degree lists are

```
21 variables: [4,6,8,5,4,3,8,6,8]
20 variables: [4,6,8,5,4,8,9,8]
19 variables: [12,14,7,7,14,9,20].
```

The following coefficients of the full sum of residual squares were
extracted exactly over the symbolic coefficient ring:

```
[Y^8 k^8] Q21 = 1,
[r^4 c^10 f^2 o^2] Q20 = 64,
[v^8 J3^24 k^8] Q19 = 2^8 3^24 beta^24.
```

They are nonzero on the actual fixed tuple (`beta>0`). Their total degrees
match twice the maximal residual degrees, proving exact degrees 16, 18,
and 40 without relying on a generic-coefficient assumption. Closedness,
variable counts, distinctness, liveness, the printed 21-variable display,
and the absence of unbound parameters were also checked.

## Replays and independent implementation

`coordinate-family-peer.py` uses SymPy's sparse polynomial rings over
`ZZ`. Its restricted arithmetic parser rejects nonpolynomial operations.
It imports none of the delivered algebra or generator modules. It checks
the complete maps, both triangular inverse directions, all literal rows,
the full coefficient certificates, original ZIP/source bytes, and all six
payloads. Normal and `-O` runs pass and agree after the mode field is
removed. A changed constant in the degree-nine auxiliary row is rejected
at the complete restoration comparison in both modes.

In separate scratch copies, the supplied `build_family.py`,
`build_coordinate_family.py`, and `check_coordinate_maps.py` each pass
normally and with `-O`. They regenerate every delivered file byte for byte,
including coefficient bindings and equations. The archive trees were not
modified. No Lean process, native machine run, consistency oracle, or
network query was used.

The accompanying JSON records exact pins, replay results, hashes, degree
data, and the ordinary semantic boundary. The new algebra transports the
authenticated parent's refutation equivalence; it does not itself close
the remaining native/compiler or internal-ZFC proof obligations.
