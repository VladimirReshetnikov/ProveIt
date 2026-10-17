# Concrete internal register-box prefixes

[`ArithmeticSymbolicBoxesPerm252`](../../Lean/BusyBeaver/ZFC/ArithmeticSymbolicBoxesPerm252.lean)
interprets the actual `SymbolicPerm252.Box`, `Effect`, `Reg` and `Branch`
constructors using the four checked arithmetic register macros. The primary
file is an externally fixed list of **nine arbitrary internal values**. It is
followed by eight zero registers, a register of value one, and an arbitrary
internal count of zero spares. The frozen boot suffix uses count 56; the
binding of this box interpretation to the whole boot frame is separate.

For an unchanged box, the prefix on an arbitrary terminal suffix is

```
fileCode (values ++ replicate 8 0 ++ [1]) (zeroBlocks count (2*suffix))
```

The factor `2*suffix` is the actual final false padding cell in native
`boxBits`; it occurs after all registers and spares. Marking replaces the
selected register's ordinary header by `00`, preserving its old value ones.
Increment replaces the original selected value by value+1. The raw decrement
effect uses truncated value−1 and count+1, matching native decrement's
unconditional appended zero block. Its execution theorem requires the
**original selected value to be nonzero**. The zero execution branch returns
an unchanged box and leaves the spare count unchanged.

The split-form endpoints reuse the already checked mark/increment/zero/
positive-decrement contracts, with the fixed spare list included in the
following finite file. Values, spare count, internal clocks and the complete
left tape range over every IΣ1 model. All execution endpoints fix the final
right exterior to zero. The prefix algebra itself retains arbitrary suffixes.
Only list lengths, the nine selectors and native syntax are external data;
this is not an internal variable-length-list graph. A separate standard-Nat
roundtrip theorem to the native `boxBits` list is not asserted here.

The four wrappers use the actual native entry and exit constructors and
check the native branch condition on the original physical primary values.
Mark returns to arithmetic state 4 for selector zero and 7 otherwise;
increment always returns to state 48. Zero decrement returns to 5, and
positive decrement returns to 63 for selector zero and 48 otherwise.
Arithmetic state codes are canonical working-state indices plus one; 0 is
halt. The finite state identities are checked from the actual constructors.
No alternate transition table is supplied.

Every concrete box starts with false. Under an explicit actual left-moving
false-write row, `box_back` performs one literal step and retains that write
and move even if its target is the halt state 0. No box execution premise is
assumed. These local endpoints do not yet prove arithmetic soundness of the
whole `checkedStep`/`sstep`/`exec`, a first-exit or dispatch invariant, a PA
consistency endpoint or a state reduction. The external 252-state endpoint
is unchanged. Mira-Cult, Jeff and Wade retain their machine/framework credit.

The [first-attempt check](results/arithmetic-symbolic-boxes-perm252-verification.json)
passes **17 ordered axiom reports and 20 generic callers**, using only standard
Lean axioms. Source and audit took 4.116 and 2.662 seconds on pinned Lean 4.32.0.
The source retains **four `unusedSectionVars` style warnings** on generic
list lemmas; the audit has zero warnings. The successful source, audit and
logs are preserved unchanged, with no proof replay for placement.

The checker merges the successful Mark 8/12 and WritingScans 6/12 records
into exactly 48 project providers, requiring shared source and object hashes
to agree. Five actual first external providers, direct Lean imports plus
Omega, all 117 input identities and the fresh object are checked before and
after. No dependency was rebuilt or downloaded.

```sh
python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_symbolic_boxes_perm252.py \
  --repo /path/to/Proofs --dependency-root /path/to/built-dependency-checkout \
  --mark-evidence /outside/successful-mark/verification.json \
  --scan-evidence /outside/successful-writing-scans/verification.json \
  --output /outside/new-empty-symbolic-box-check
```

The maintained checker is byte-identical to the executed original. `--cache`
relocates all 48 selected project objects with identical hashes. The default
preflight is **PREPARED_NOT_BUILT**, with no compiler commands. Python `-O`, a
nonempty output directory and a shadowed first Omega provider are separately
rejected without proof compilation. The [publication record](results/arithmetic-symbolic-boxes-perm252-publication.json)
keeps the proof, preflight, controls and warnings distinct. The
[independent review](results/arithmetic-symbolic-boxes-perm252-review.json)
binds the native constructor/guard review, final source and audit, selected
providers, unchanged portable checker and preflight.
