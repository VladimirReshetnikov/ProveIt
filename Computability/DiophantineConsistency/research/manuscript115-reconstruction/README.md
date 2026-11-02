# Reconstructing the manuscript 115 supplement

Manuscript 115's main construction is a 358-variable quartic over the
nonnegative integers, using the direct C222 calculus. Its separate supplement
reports a 12-positive-variable, 95-operation, degree-70 equation and four
other positive-domain circuits. These are different constructions. The main
manuscript presents an ordinary mathematical argument and expressly does not
claim a sealed object-language proof; this note does not review its full C222
argument.

## Missing files and reproducible reconstruction

The tracked supplement is incomplete: 18 of the 45 files listed in its
`MANIFEST.json` are missing, including its coefficient binding and four
payloads, two parent graphs, and four inherited proofs. Running its checker
directly exits 1 on the missing `p13_free_J.json`, before reaching coefficient
binding or graph checks. Its committed PASS receipts are therefore not a
reproducible check of the shipped files as they stand.

`check.py` copies the supplement to a temporary directory and retrieves each
missing file from the available historical Git commit
`84e16e43092614bae262ca59651cb9d77e31a255`. It checks every existing and
restored file against the supplement's manifest before using the restored
files. The receipt lists each missing destination, exact original repository
path, and SHA-256. No supplement source or historical receipt is modified.
The reconstruction depends on that Git commit being available locally; it
does not use the network. Both the normal and optimized reconstruction runs
finished with exit 0, and each ran the unmodified supplement checker in both
normal and optimized Python with exit 0.

## What the graph check establishes

The checker in this directory separately compares the 12-variable graph with
the frozen 96-gate parent. It checks binary-gate topology, operation counts,
full liveness and input/output agreement, expands the changed carrier cut in
an exact integer polynomial collector, and propagates equality through all
remaining gates. Its identity uses `M=q3*qm`:

```
M*g31 + qm*Y - q3*(1+k*qm)*Bt
    = M*(g31-k*Bt) + qm*Y - q3*Bt.
```

This verifies pointwise identity over arbitrary integer values of the twelve
inputs and four ports, and therefore the same positive-integer zero set as
the pinned parent. All 95 gates are live: 52 multiplications, 25 additions,
and 18 subtractions, counting each binary gate once and fixed numerals as
free leaves. The restored supplement's own different exact-cut checker agrees.
Neither this check nor the supplement independently proves exact degree 70:
the supplement transports it from the parent, while its direct syntactic
degree bound is 82. A subsequent [independent audit](../../reviews/manuscript115-reconstruction-independent-audit/README.md)
established exact degree 70 using structural cancellations for the upper
bound and a nonzero diagonal coefficient computed from the exact fixed ports.
The reported ordinary equivalence remains inherited from the parent arithmetic
and its native/compiler calibration, not proved by this finite graph identity.

The parent free-J proof changes a constrained witness to an arbitrary positive
`J`; it is an ordinary two-direction arithmetic argument, not pointwise
identity with the earlier restricted-witness polynomial. The separate
polarization and carrier-cut steps are pointwise identities. An internal iPRA
proof requires additional work: exact positive-domain model transport,
binding and calibration for this coefficient tuple, and a syntactic
object-theory proof. See [the current bridge plan](../ordinary12-ipra-bridge/PLAN.md).
No such proof follows from the reconstructed checker.

## Fixed tuple

The recovered binding's four decompressed raw payload hashes agree with the
binding in `98-congruence-certificates/positive/coefficients/BINDING.json`.
It has `beta = 2^590069 - 1`; `MF` is already shifted. Thus it differs from
the audited 2011 fixed tuple, whose beta is `2^94517 - 1`.

Names alone do not identify the entire tuple. The independently supplied
`research/saturated-direct-carrier-cse/coefficients/compact44_bfs` payloads
agree byte-for-byte on beta, MC and MF but **not** K0. The recovered K0 raw
SHA-256 is `c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e`;
that alternate payload is
`4364134a56b54cf132beeb9acd8e832be68f9083f4359ace4a588a1ea76a60f7`.
The graph identity is port-parametric, but the fixed-port ordinary and iPRA
claims must be calibrated to the exact chosen four integers. A shared beta or
the label `compact44` does not establish that calibration.

Run from the repository root:

```sh
python3 -B Computability/DiophantineConsistency/research/manuscript115-reconstruction/check.py
python3 -B -O Computability/DiophantineConsistency/research/manuscript115-reconstruction/check.py
```

These reconstruction checks provide finite evidence for the literal graph and
payloads; they do not prove the remaining ordinary-equivalence dependencies.
