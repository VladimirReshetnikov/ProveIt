# Nine more paid operations removed by shared binary affine planes

The [narrow source transformer](u15_joint_binary_affine_rewrite.py) replaces the complete seven-projection affine block by **90=4M+86A gates**, down from 99=12M+87A. It saves **eight multiplications and one addition**, preserving every comparison and the complete emitted polynomial on every supplied integer tuple. Applied to frozen 536, it emits **527=211M+316A** ordinary operations and **329=118M+211A** raw operations. No rule label, witness, comparison, positivity condition or native kernel changes.

The [receipt](u15_joint_binary_affine_rewrite.json) includes both complete rewritten sources, their SOS finalizers, exact affine vectors, the literal gate ledger and complete downstream-DAG identity certificates. This is a reusable arithmetic transformer, not a new canonical full compiler or a new universality theorem. Its result can be composed with independent downstream transformations that satisfy the structural contract below.

## Exact construction

Let `h_i=edge_i`, for `0<=i<29`, be the original positive edge hats. The seven required forms remain

```
J    = sum h_i - 29,
S    = sum read_i*h_i - 14,
Dir  = sum direction_i*h_i - 15,
W    = sum write_i*h_i - 17,
WD   = sum direction_i*write_i*h_i - 9,
Qdev = sum (source_i-7)*h_i - 6,
Ndev = sum (target_i-7)*h_i + 17.
```

For an integer coefficient `a` between -7 and 7, write its ordinary magnitude bits as `|a|=b0+2*b1+4*b2`, and retain its sign. Define `Qj` to be the signed sum of hats whose `j`th magnitude bit is set in `source_i-7`; define `Nj` identically for `target_i-7`. Then

```
Qdev = Q0 + 2*(Q1 + 2*Q2) - 6,
Ndev = N0 + 2*(N1 + 2*N2) + 17.
```

The complete literal schedule shares sums and differences across these six signed planes and the five Boolean-table projections. Its first 75 additions/subtractions produce the eleven unoffset forms. Four multiplications by 2 and four additions implement the two Horner expressions; seven offset operations finish the seven cuts. The total is therefore 4M+(75+4+7)A=90. Multiplication by 2 is charged, not treated as free.

The source includes all ninety binary rows literally. Their unoffset output nodes are:

| Form | Literal node |
|---|---|
| Sum of all hats | `binary36` |
| Read sum | `binary40` |
| Direction sum | `binary42` |
| Write sum | `binary44` |
| Direction/write sum | `binary15` |
| Q0, Q1, Q2 | `binary51`, `binary55`, `binary62` |
| N0, N1, N2 | `binary66`, `binary71`, `binary74` |

For clarity, the signed-plane supports are:

| Plane | Positive hat indices | Negative hat indices |
|---|---|---|
| Q0 | 16,17,19,20,23,24,27,28 | 0,1,4,5,8,9,12,13 |
| Q1 | 2,3,19,20,25,26,27,28 | 0,1,8,9,10,11,18 |
| Q2 | 21,22,23,24,25,26,27,28 | 0,1,4,5,6,7,18 |
| N0 | 14,18,21,26 | 1,2,3,4,5,7,8,13,15,16,25 |
| N1 | 0,18,20,23,26,27,28 | 1,3,5,6,7,8,16,17 |
| N2 | 19,20,21,22,24,26,27,28 | 1,2,3,8,9,10,11,16,17,25 |

These are signed computed expressions; they are not new natural or positive witnesses. The identities hold on arbitrary integer hats, with no one-hot or history assumption.

## Complete polynomial identity

The transformer expands the old and new seven cuts as exact integer affine vectors in the 29 hats plus the constant coordinate. It requires all seven vectors to agree. It then replaces outgoing references through those cuts, retaining every other source row and every comparison.

A separate expression-DAG certificate substitutes formal names for only the seven already-proved equal vectors, interns the complete old and new emitted polynomial sources, and compares all comparison operands, semantic/tag/computed-loader registers and the final SOS output. Thus equality holds for each residual and for the entire polynomial on every supplied integer tuple. It is a polynomial identity, so it also holds over the rationals and reals. No retained equation or zero-set assumption is used.

The complete cost on 536 is:

| Interface | Certificate | Finalizer | Complete polynomial | Positive witnesses / comparisons |
|---|---:|---:|---:|---:|
| Raw | 297=107M+190A | 32=11M+21A | **329=118M+211A** | 51 / 11 |
| Ordinary | 435=180M+255A | 92=31M+61A | **527=211M+316A** | 87 / 31 |

The rebuilt ledger records degree upper bound 1936 and makes no new exact-degree assertion. Exact degree transfers from 536 through the complete polynomial identity. The separate universal 87-operation benchmark is unchanged.

## Reusable interface and guards

`replacement()` returns a fresh list of ninety rows and a fresh cut-name map. `rewrite(packet)` returns `(fresh_packet, proof)`.

The arithmetic contract requires the exact literal 99-row affine closure, the seven incoming cut registers and the same 29-rule table. It accepts independent downstream edits, reordered source rows, changed comparison lists or compatible coordinate changes. It checks the complete source and literal stored SOS, exact integer arithmetic atoms, distinct input declarations, topological closure, unique node names, and absence of dead emitted gates. It rejects any private removed affine intermediate used by another source row, comparison or metadata value; only the seven cuts may escape. Name collisions with new `binary*` rows are rejected. All outgoing cut references, including nested metadata references, are replaced, and all returned data are copied.

This contract is deliberately local to the arithmetic block. It does not certify the semantics of an arbitrary caller's downstream modifications or claim that the result is a canonical packet of the caller's original public compiler. A maintained composition should supply its own canonical full-packet guard, parent descriptor and semantic relation, as the 536 composition did for the preceding affine transformer. There is no fixed 536 operation-count assumption inside `rewrite`: it verifies the relative saving of exactly 8M+1A. Only the standalone replay checks the absolute 527/329 ledgers.

## Bounded search and replay

The finite search tried 500 deterministic tie-breaking seeds for each of three representations: direct signed coefficients, signed ordinary magnitude-bit planes, and signed nonadjacent magnitude digits. Their best complete affine counts were respectively 98, 90, 96. The selected circuit is ordinary binary planes with seed 58. This is evidence for an explicit schedule, not a minimum-circuit claim or exhaustive search over all arithmetic circuits. The maintained transformer stores the selected circuit literally and does not rerun or depend on the search.

The standalone replay authenticates the frozen 536 source SHA-256
`eaaf3d99e74efeec26b7ad50842ac95fc89273f5ba37a52d45e9cca0e8fde330`
and complete receipt SHA-256
`5a734c98ad6c6cda6efa5ced74ff7617e305419f11d9d960def8b292c83d0023`.
It performs two exact full-DAG identity checks, 64 complete output/residual evaluations including 32 signed tuples, 38 malformed-source rejections, 8 defensive-copy checks and 4 compatibility-adapter checks. The adapters reorder the independent affine block and add a new legal cut consumer with a metadata alias. Invalid private consumers in source, comparison or metadata are rejected. A fresh replay matched the full saved JSON byte for byte.

From the maintained artifact directory:

```sh
python u15_joint_binary_affine_rewrite.py \
  --parent-source u15_packed_joint_affine536.py \
  --parent-receipt u15_packed_joint_affine536.json \
  --expect u15_joint_binary_affine_rewrite.json \
  --output u15_joint_binary_affine_rewrite.fresh.json
```

The CLI requires explicit paths and assertions, and imports no parent module or temporary helper. The exact affine and complete DAG proofs establish the all-value identity; finite evaluations only corroborate the emitted arithmetic.

The integrating review read the complete helper and note, independently reconstructed all seven 30-coordinate affine vectors directly from the literal machine table, and confirmed a fresh full author replay against the saved receipt. No unresolved arithmetic or source-contract finding remained.
