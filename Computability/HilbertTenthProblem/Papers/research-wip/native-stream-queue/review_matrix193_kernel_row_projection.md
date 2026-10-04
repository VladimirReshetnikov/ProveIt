# Independent review of the kernel-row193 target interface

**PASS; no finding.** The entire frozen author helper and proof were read. The independent standard-library checker reconstructs all old and new matrix entries from pinned data without importing or running the author or predecessor helpers. Fresh receipt replays from `/` passed normally and under `python3 -O`.

## Frozen author and dependency scope

| Author file | SHA256 |
| --- | --- |
| `matrix193_kernel_row_projection.py` | `2eb89dfae4e9352fa67c707109853c025c823ab34869bc25f54912736734d105` |
| `matrix193_kernel_row_projection.json` | `543d461a50bc1bb31c1e8bcc60ede58a5e9815b194ddd49c5640e3a50611caeb` |
| `matrix193_kernel_row_projection.md` | `400aab15caa9462808cc2dc2ef68f013797a9bc656c97acecdd610de81a13c6e` |

The reviewer authenticates these bytes, the author's self-source hash, and all six exact dependency pins. The dependencies are the JSON/proof pairs for [the original193](group_directed_semigroup193.md), [Schreier1057](matrix193_schreier_recode.md), and [the unary-block interface](u15_unary_block_interface.md). No original U15 universality proof or arbitrary-program compiler is newly audited here. The retained directed-word construction and indexed input theorem are inherited from those pinned reports.

## Mathematical review

For the free matrix group `F=<P,Q>`, with `P=[[1,2],[0,1]]` and `Q=[[1,0],[2,1]]`, let `K` be the kernel of the Q-exponent homomorphism. If M,N in K have the same first row, then `NM^-1=[[1,0],[k,1]]`. Membership in the identity-modulo2 group makes k even, and this is `Q^(k/2)`. Its zero Q-exponent forces k=0. This argument proves injectivity on the entire subgroup, including inverses; the finite word checks are not its justification.

The expanded words `E_j=Q^-j P Q^j` freely generate because adjacent distinct indices leave nonzero intervening Q powers between nonzero P powers. Replacing E0 by `a=E0 E1^-1` and retaining `b=E1` is an invertible basis change, with `E0=ab`. Thus all twenty upper letters, not just the tape pair, retain faithful encoding in K.

Both blocks of every one of the193 new generators lie in K: the upper block uses only the new letter group, while the lower blocks are E_i, `P^-1 E_i^-1 P`, and P. Their products remain block diagonal and in K. Consequently the two lower first-row constants recover the full lower target P, and the two varying upper coordinates recover the full upper target whenever those coordinates come from the specified word target. This proves exact projected membership for the actual fixed semigroup. It does not identify arbitrary SL4 matrices from four observations.

The unchanged tiles and lower marker force the same directed word equation, and the full faithful alphabet recoding reflects that equation in both directions. The inherited valid-input acceptance reduction therefore survives. Enumerating nonempty matrix products gives the claimed c.e. upper bound. Together with that inherited reduction, the pair-valued predicate is c.e.-complete. No empty product or extra identity generator is introduced.

The original193 encoding also lies in K and admits this projection. The author correctly distinguishes the new row projection from the new numerical recoding; the earlier1057 encoding contains Q², which defeats this particular row-injectivity argument.

## Independent arithmetic and source checks

The reviewer uses the direct entry formula

`E_j=[[1+4j,2],[-8j²,1-4j]]`

and flat four-entry matrix arithmetic. It reconstructs all193 original matrices and all193 new matrices, retaining every rule, tile, identifier, terminal and lower block. All3,088 entries in each array match; all new matrices are distinct, and both blocks have determinant one and the required parity. The exact new ledger is:

| Resource | Value |
| --- | ---: |
| Generators / integer entry slots |193 / 3,088|
| Nonzero slots |1,543|
| Largest absolute entry |371,425,216|
| Largest magnitude bit length |29|
| Sum of magnitude bit lengths |19,888|

The inherited167-generator accepted word is multiplied in both complete2×2 blocks and matches the saved4×4 target in every entry. This finite witness corroborates the general recoding proof; it does not establish universality on its own.

For `W=01010111`, the independent reconstruction gives

`Psi(W)=[[-87,-38],[-16,-7]]`,
`B=Psi(W)^2=[[8177,3572],[1504,657]]`,
`a0=4417`, and `(B-a0 I)^2=(a0²-1)I`.

Binary matrix powering independently checks all thirteen displayed negative powers against the Pell recurrence. For100 fixed diagnostic context pairs at each of those thirteen indices, the reviewer compares the complete literal word target with `L B^-x R` and with the two outputs of the six paid instructions. All1,300 comparisons pass.

The literal six-row source is checked independently, including operation/port liveness. A small formal polynomial calculation proves each output is exactly `chi*C1j-psi*F1j`; the ledger is **4M+2A=6**. The complete source is an upper bound for generic supplied fixed context coefficients. No arithmetic minimality or nonzero-coefficient condition is claimed.

## Boundary and replay

The six operations assume correctly indexed Pell coordinates. The index relation and an unbounded product certificate are not included. No fixed-arity polynomial for the projected matrix predicate is emitted, and no conversion of signed target integers to a natural input interface is priced. The established universal-operation bound is unchanged.

The reviewer is a bounded reproducible CLI. It rejects duplicate JSON keys and nonfinite constants, checks hashes before reading pinned data, uses explicit exceptions rather than optimization-sensitive assertions, and compares receipts recursively with exact types. It does not advertise a maintained compiler API.

With the author and reviewer trios installed in one research directory:

```sh
python3 /absolute/path/review_matrix193_kernel_row_projection.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/review_matrix193_kernel_row_projection.json
python3 -O /absolute/path/review_matrix193_kernel_row_projection.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/review_matrix193_kernel_row_projection.json
```

During external review, `--author-root /absolute/path/author-directory` selects the separately staged author trio; dependency files still come from `--root`. `--output FILE` writes the deterministic review receipt instead. Both fresh normal and optimized staged replays passed on the frozen author pins above. No predecessor code, archived executable, historical suite, or arbitrary-program compiler was run.
