# Bounded one-new-rational-leaf screen for the 64-row evaluator

**Coefficient scope:** this screen uses the fixed ports from the
`one-page-reversed-carrier65-2521` package. They are **not** the current14
beta and masks. The result says nothing about a fixed-current14 search.

This screen looks for a pointwise polynomial-preserving reduction of the
checked 64-row rational-leaf evaluator by replacing **one** target row,
requiring the replacement to equal that intermediate row at every sample,
then deleting dead rows. It does not enumerate replacements that preserve
only the final output through cancellation or an insensitive suffix. The
four reversed2521 source integer ports are read
from hash-checked compressed files. The existing runtime leaves are
`beta`, `K0`, `Urank = MF / beta`, and `Wrank = MC - MF`; the division is
performed modulo each sample prime. The 14 witness values are sampled
independently. The screen allows **one additional fixed rational leaf**
`c`, independent of all witnesses, whose residue may depend on those fixed
reversed2521 ports. It treats construction and storage of all fixed leaves as free and
places no bit-size bound on the hypothetical extra leaf. Thus the family
permits up to five fixed runtime leaves plus ordinary literals 0–4; it
does not measure an integer-leaf operation or storage improvement.

The enumerated replacements are: a direct fixed leaf or earlier-node
alias; one gate `x+c`, `c-x`, or `c*x`; and two gates `c*x+y` or
`c*x-y`, where `x` and `y` are earlier leaves or graph nodes. The
coefficient residue is inferred independently at each of three checked
primes from four assignments and verified at every other assignment for
that prime. Survivors would be candidates only and would require an exact
symbolic identity and Lean proof; no survivor is certified by this screen.
The final result contains **no replacement with fewer than 64 live rows**.
It checked 64 targets, 64 constant and 3,488 alias cases, 10,400 one-gate
and 416,896 two-gate affine queries. There were 124 modular survivors
among the one- and two-gate affine forms before the live-row test; that
counter does not include constant or alias survivors. There was no
unresolved zero-scale sample and no
nonliteral zero scale. A small constructed `x+1+2` positive control was
reduced to `x+c` as intended.

This is a finite modular filter, not a Lean theorem or a global operation
lower bound. Its exclusions assume that any candidate coefficient has a
well-defined reduction modulo all three selected primes; a rational whose
reduced denominator is divisible by a sample prime is outside that claim.
The screen does not cover multi-row coordinated replacements, arbitrary
two-gate expressions such as `(x+c)*y`, nonlinear uses of the new leaf,
multiple new constants, changed witnesses, or equivalence only at zeros.
Sampling collisions could create extra candidates, but no candidate is
promoted without an exact check. No 63-operation candidate was found in
this family and the maintained 65-operation integer equation is unchanged.

From the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/research/rational-carrier64-affine-leaf-screen/screen.py
```

The pinned graph SHA-256 is
`8fd205a43c4045914d88f4117ba263cf7a232ac26c64dcf09a1c37a8d88e7b27`.
The stdout receipt includes the three primes, seed, source graph and
compressed port hashes and an explicit reversed2521 scope field. The saved
outer session 67386 exited 0; it was a
low-priority run with a 120-second timeout and stdout redirected to the
saved `result.json`. The prior scope-unlabelled run is retained in
`observations/attempt01/`; its screen and positive-control data are
identical. No Lean process was invoked.

| Artifact | SHA-256 |
| --- | --- |
| `screen.py` | `4a11bfec6db2a1cee0d87f71c02fe7cd04f27385001e906cf84616c05201f2fe` |
| `result.json` | `edd8cbe67b46296ee9b9ae91fd5bbab95a5f09810e5e3dd10ef195d591198638` |
| `outer-terminal.json` | `05ed6feb7b30c05634538a285b0722cbd5d2064944aea42bcbd8ddfbe82577b9` |
