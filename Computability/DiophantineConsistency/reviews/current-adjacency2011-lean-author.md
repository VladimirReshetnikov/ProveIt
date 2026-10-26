# Current adjacency: author implementation receipt

Date: 2026-10-26 UTC. Author: `controller_certificate`, at root's assignment.
This is an author receipt, not an independent peer review. No frozen module,
maintained equation, or umbrella import was edited.

Frozen source bindings:

| File under `Lean/DiophantineConsistency/` | SHA256 |
| --- | --- |
| `CurrentAdjacency2011.lean` (213 lines) | `160cef12e27cda2ece581ba0acfb2fcbbf194d918fe75d630705a7feb8e97133` |
| `CurrentAdjacency2011Checks.lean` (64 lines) | `9588fc2cb97226e1b802fef9042d7287865d62f50b4b05d8454a2368b2be4939` |
| Imported `CurrentCopyParity2011.lean` | `dc49658f1d9c448eca9ff969336cd5f64b4f64483b47b48d72f3a6bd0d928c8a` |
| Imported `CurrentReflectedGeometry2011.lean` | `268ecac628932a93d79593ae0b4e1c8819817db58f27ec9613c4ad23a29d60c1` |
| Imported `CurrentOneHot2011.lean` | `45e9cd33fb50e4fc16f524948fc2f68a4dfbd334dd64e7fda114b3c55946842c` |

I read the complete copy-parity, reflected-geometry, high-digit modules and
copy-parity checks before implementing this packet. Both complete new files
were read before final execution; the single later check correction was
also read before its replay.

The conditional normalized-word interface takes the actual Boolean sparse
word, carry bound57, full carry recurrence and local equation, the actual
high-mask tests, and the physical selector count at most one in the current
aligned cell. It assumes only the two phase conclusions `W%47=0` and
`(W/47)%2011=0`. It does not assume a carry reset, occupation, decoded labels,
a marker value, or a tableau.

For each `j : Fin 8`, the target is `b+987+j`. The complete convolution is
proved equal to current East at `b+969+j`, previous-cell West at
`b-2011+978+j`, and the full reflected sum. The bare1004 input has residue
`1994+j` and vanishes by the actual low support. The aligned temporal input
has residue `987+j`, which is also outside that support. Both removals use
proved cyclic residues and remain valid at cyclic wraparound.

The incoming carry is derived from the existing literal reflected bound
using the physical count and unconditional Boolean temporal bound. The
reflected sum is retained until its evenness is applied. The actual mask
digit is1 at all eight targets, including987 and994. Reducing the complete
local equation modulo2 therefore shows that the two retained Boolean bits
are equal. Thus the orientation is precisely

```
current East969+j = previous-cell West978+j
```

The existing nine South-copy equalities are specialized without changing
their reflection argument. They become

```
current South942+j = temporal-cell North960+j
```

Here `previousCell b = b-2011` and `temporalCell W b = b-(W/47)` in
`ZMod (N*2011)`. Both source bases are proved aligned. The temporal base is
also proved equal to `b-2011*((W/47)/2011)`, including zero stride and shifts
larger than the cyclic length. No positivity of this stride is asserted.

`facts_adjacency` specializes this interface to the same original polynomial
window and rank-derived shift `core.rank.toNat-47*(N*2011)`. It obtains the
fractional phase and count from `CurrentOneHot2011.facts_count_phase`.
Whole-field alignment remains its one explicit additional premise. The
same original `v`, source `x`, word, carries and normalized digits are used
throughout.

Focused checks include exact two-cell source addresses and both endpoint
mask fields, the unmasked field995, the one-cell horizontal wrap, and zero
temporal stride. A separate check shows that fractional phase zero alone
leaves the horizontal temporal term at a shifted low field for shift19;
the whole-field alignment premise is therefore material to this proof.

Fresh sequential commands, with Lean `v4.32.0`:

```sh
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentAdjacency2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentAdjacency2011.lean
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentAdjacency2011Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentAdjacency2011Checks.lean
```

Both exited zero. The main diagnostics are empty, SHA256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The checks log SHA256 is
`4a27969b17e5fd7762283352d238cc2ee161786bf27b707b6610c77c5dd6631a`.
All six axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound` (the stride theorem needs no choice). No custom or native
evaluation axiom occurs.

Development history: the main proof passed its first compile. The initial
one-cell focused check needed the explicit numeral identity
`(2011 : ZMod (1*2011))=0`; supplying that identity resolved the check without
altering any theorem or premise.

Scope: these are exact physical bit equalities. Converting them to matching
decoded tile colors, proving occupation and positive temporal stride, and
constructing a finite native-language certificate remain separate steps.
No native-language or consistency endpoint is claimed here.
