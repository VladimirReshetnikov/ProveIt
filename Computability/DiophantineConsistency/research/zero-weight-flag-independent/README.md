# A physical flag with zero clause weight

[PROOF.md](PROOF.md) supplies the complete ordinary native inverse,
fresh cofinal converse and both positive P66 witness maps for a new
four-integer tuple. It retains fifteen positive unknowns, 66 integer-leaf
operations and degree 157. The new ordinary argument is relative to the
retained explicit arithmetic, complete syntactic-refutation and foundational
contracts. Soundness uses no new finite controller premise; completeness
uses exactly Pc0 in section 11. **Pc0 is now numerically discharged for
this exact tuple**, and the [independent full mathematical review](../../reviews/zero-weight6007-independent-peer.md)
passes within those retained contracts. The complete proof remains frozen
with its original conditional formulation for provenance.

The physical flag at 1984 remains in the mask but has coefficient zero
in both clauses. Each 43-bit clause recovers the empty state or a unique
tile with all labels, without constraining that flag. In the forced Start
cell, the calibrated south-bit copy at 974 and selector count at 1984
both equal one. Their parity tests recover alignment. The aligned count
test then equates the temporal flag with the current selector count;
spatial label equality propagates occupation, which finally forces every
flag to one. That order of recovery is essential.

The labels use S943..951, N973..981, W992..999 and E1002..1009; the
dummies are 990 and 991. Bare shifts 20 and 30 and spatial shift 10
give all 17 exact copies. The 943-term selector-count block is
`rho^1042 G_943(rho)`. Its nonflag products end at 2993, and its flag
products occupy 3026..3968. Thus neither it nor its carries disturb the
clauses at 2995 and 4007 after the proved predecessor resets.

There are 980 physical positions and 977 nonzero weighted coefficients.
Core population is 105; padding contributes 875 bits in 18 full fields
5019..5036 and the low 29 bits at 5037. The full zero band 5019..5039
and its predecessor 5018 are proved. The last product field is 5991;
the fixed cell length is `L=6007`, with `d=282329`.

The shared control polynomial is

    Psi(x,t)=x^992*(x^10+t^17)*G_8(tx)
             +t^8*x^943*(x^30+t^17)*G_9(tx)
             +t^34*(2-t)*x^1984.

Psi at one includes the physical flag; Psi at two omits its clause
weight. Consequently physical support must be taken from the explicit
support or Psi-at-one recipe, never inferred from nonzero Phi alone.
The new coefficient sum is the preceding weighted-flag sum minus 3M.
One global carry bound 29 covers all phases, empty flag choices, copies,
predecessors, padding and origins. The proof includes the actual binary
rank, simultaneous safe subsets and exact ordinary rank increments.

## Complete finite discharge

The separately authored [certify.py](certify.py) binds the complete proof
and the exact reviewed predecessor verifier before construction. That
predecessor also binds its full proof, complete seed page and decoder.
The new verifier explicitly retains the zero-weight flag in physical
support and distinguishes Psi at one from Psi at two. It checks all
copies, complete clauses and predecessors, the unit-product gap, every
padding field and top reset, complete scalar boxes and mask populations.
The full Boolean convolution and both extra low-dummy units are included
in an additional exhaustive finite envelope. That check is separate from
the proof's unbounded cyclic carry argument.

Trial division and all proper-divisor tests give exact orders 23 and
`1001=7*11*13`, spacing 23023, and
`lambda=368369=16*23023+1>d=282329`. Reciprocal Horner, direct positive
powers from the complete tiles and labels, and whole-integer reduction
agree on K at all relevant moduli:

| Modulus | B | K | H = 1+BK+B² |
| ---: | ---: | ---: | ---: |
| 47 | 16 | 34 | 2 |
| 6007 | 5053 | 4606 | 53 |
| 368369 | 315712 | 25722 | 95646 |

The auxiliary square is 46186, and the exact valuation-one lift is
`135511167293=1+lambda*367868`, with `0<367868<lambda`.
The frozen verifier SHA256 is
`35669d519f1fdd283e7b498d36cc799f10a3bdc7b4924f40ce011724fe3942c5`;
[certificate.json](certificate.json) has SHA256
`6b25d6e2581822894fdc429bf4639ff009fa134599b8e569ee4b94de046afe5a`.
After reading all 368 lines of the separate verifier, the mathematical
author ran both commands below. Both read-only checks exited zero and
reproduced the entire certificate and coefficient array exactly.

```sh
python3 -B Computability/DiophantineConsistency/research/zero-weight-flag-independent/certify.py
python3 -B -O Computability/DiophantineConsistency/research/zero-weight-flag-independent/certify.py
```

No `--write` option was used. Explicit exception guards survive
optimization. This author check does not replace the independent
mathematical review, whose SHA256 is
`631783984bc71ff66d35c6473d324571183f378ab7a8962845693ef6acceee37`.
The complete minimal unsigned big-endian ports are:

| Port | Bits | Bytes | SHA256 |
| --- | ---: | ---: | --- |
| beta | 282329 | 35292 | `3de315e250147d48d8f5dd9171583d3cbd9d079b13bff1bc20d5630419ebf5f6` |
| K | 282800 | 35350 | `2294c5c9d900a107cb100896425808fb428486a9ab7fb0eb2a372d5bca4ddc4b` |
| MC | 282329 | 35292 | `8a5ab5d3b8e0ed02e82a841ca4907241d3e4f254e6665251e048cb38c5930eaf` |
| MF_source | 282330 | 35292 | `395022d0afcb0dfbf99cae12116d95cfe47d2488d3b1c866a0df8a2f93f93161` |

Their total is 141226 raw bytes, compared with 172011 for one-anchor7309.
No preceding controller certificate is reused, and no printed-size claim
follows from raw-byte size. Rendering and source-size comparisons belong
to a separately constructed and reviewed complete candidate page.

The complete ordinary proof SHA256 is
`ccfbcea8c2dd5502e896777f20234bddd23e16cf43cb67d267131258d3d753d7`.
ROOT supplied the zero-weight flag and delayed-recovery lead; the proof
author supplied the nonuniform label/dummy layout. Separate authors own
finite implementation and independent mathematical review. No earlier
accepted proof or page is changed. This research claims neither global
minimality nor actual unsolvability nor a new end-to-end proof-assistant
or internal-ZFC formal replay.
