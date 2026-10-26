# Root review of the displayed decimal machine and padding arithmetic

ROOT independently read all four complete new sources, the exact current
TeX decoder, and the invoked dense-machine simulation interface. Both
packets pass fresh ROOT compilation and focused checks. The decoder was
authored by `/root/circuit_reduction`; the staircase was authored by
`/root/complemented47_review`.

| Source in `Lean/DiophantineConsistency/` | SHA256 |
| --- | --- |
| `DecimalMachine215.lean` | `da9e49c1a5f47a10d1f385810e1e89d2e3f4f25fc438dc85cf2184efdc3c719a` |
| `DecimalMachine215Checks.lean` | `8aa431e5c18b2aa3183838b6f0878561a454a59b2a9f161e7838313727388b9f` |
| `PaddingStaircase.lean` | `b75d9c9cf430b4e3f8b020246c75eefd9c367f740cc6b1a99bc5de4859fb4932` |
| `PaddingStaircaseChecks.lean` | `613885b7de19ab5d954c4e088a5d8655bc0b2354ab954d0da9042b4282f0063e` |

## Literal decimal machine

ROOT extracted every decimal line of the actual maintained TeX and
compared the resulting715 digits with the entire Lean seed numeral: exact
equality, TeX hash
`a48ac1f5bc498bfdbf300c7050332ecaa28af1fc43f27d86b0879a79bd38714e`.
The recursive counts and products are proved equal to the displayed finite
sums and products, including endpoint430. Targets subtract over integers
before taking modulo216. In particular action125 has raw target−1 and
halt sentinel215; truncating the subtraction would change the machine.
The constructor's actual first target is1.

The discovery-order machine is not assumed equal by state index to the
dense machine. Two complete inverse state maps give an explicit215-state
equivalence fixing zero. All430 writes, moves and optional next states
are checked to commute. The existing dense-to-zipper bridge then gives
blank-halting equivalence, without assuming either machine halts. No
tile-language or consistency equivalence is used as a premise.

The focused checks include the complete decimal length,214 discoveries,
71 flag exceptions, first action, renamed state1, and the signed halt
case. The two main axiom reports contain only `propext` and `Quot.sound`.
The exact six-module source-identical dense dependency cache is recorded
separately in `decimal-machine215-dependency-cache.json`; it does not
stand in for a current full KEndpoint215 rebuild.

## Actual bit and clause tests

The staircase proof starts at prefix zero and allows only Boolean
increments. If a checked prefix first reached4, its tested value would be
8,9 or10, each with bit3 set. Induction therefore bounds every checked
prefix by3. Equality modulo16 is sufficient for the actual bit test, and
masking by8 is proved equivalent to that test. The finite-sum application
uses all483 prefix tests and all459 remaining Boolean selectors, yielding
total at most462.

The actual complete clause mask `2^45-4` implies its low mask2044.
With carries at most57, bare unit at most1 and temporal low term at most
1024, the whole low total is at most2006, strictly below2048. Thus modular
reduction cannot hide an additional count; the low mask forces total
selector count at most1. No bound on the high weighted label word is
silently inserted. Booleanity, the physical digit/residue identities and
carry/unit bounds remain explicit, to be derived from the literal kernel.

Focused checks show that the final prefix test alone is insufficient,
why the additive budget matters, invariance under arbitrary multiples16,
the n512 phase10 wrap obstruction, and an occupied full-mask clause.
The axiom reports contain only standard `propext`, `Classical.choice` and
`Quot.sound`; no admission, new axiom or native-decide extension appears.

ROOT freshly checked each main module with `lake env lean ... -o ...`
and each corresponding check module with `lake env lean ...`. All four
commands succeeded. The complete current coefficient and tile binding,
phase and whole-field alignment, helical soundness/canonical completeness,
and final consistency equivalence remain open. These modules close exact
machine-data and staircase-arithmetic obligations, not those remaining
native/compiler requirements. The maintained decimal page is unchanged.
