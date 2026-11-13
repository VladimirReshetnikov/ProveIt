# Conditional high-mask origin transfer

`CompactHighOriginTransfer.transfer_parts` proves in every IΣ₁ model that
`NoCarry (4*a) (8*b+4)` implies `NoCarry (4*a) (8*b+3)`. The proof
separates the relevant low bits using the existing `noCarry_binary` theorem;
it does not inspect the rest of either number.

`CompactHighOriginResidue.transfer_residue` derives the same result from
`x % 4 = 0`, `m % 8 = 4`, and `NoCarry x m`. Its
`symbolic_high_origin` specialization uses the existing model theorem
`highNat % 8 = 4`, showing that the special `NoCarry x (highNat - 1)`
condition follows from `x % 4 = 0` and ordinary `NoCarry x highNat`.
**Both premises remain to be proved for the actual `blk 0`; no high-mask
packing field, graph zero, or iPRA theorem follows from this client alone.**

Both the generic client and the corrected residue client compiled on a
single-author provider with guarded direct inputs and unchanged companion
records, no warnings and no `sorryAx`. The first residue attempt failed on a
rewrite that also changed an occurrence inside the quotient; its source and
compiler log are retained. The corrected successful attempts have tool
sessions 29801 and 72817. All three named axiom reports list only `propext`,
`Classical.choice`, and `Quot.sound`. Exact source/object hashes, dependency
scans, commands, logs, and terminal records are in `observations/`. Provider
transitive, package, dynamic and between-observation ancestry is inherited;
`/tmp` provider paths are ephemeral. No paired replay or complete closure
audit is claimed.
