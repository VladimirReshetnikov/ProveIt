# Root review of bounded cyclic carry and word normalization

Result: PASS for the stated arithmetic interfaces. Author:
`/root/complemented47_review`; independent source reviewer and replay: ROOT.
All four new sources were read completely before acceptance.

| Source in `Lean/DiophantineConsistency/` | SHA256 |
| --- | --- |
| `NativeCyclicCarry.lean` | `25c08e2b6b10e72fe9b3d4df81078e4e1e5ede8e3e94b9666dc5616dcfebc72e` |
| `NativeCyclicCarryAudit.lean` | `00914cded40704260aaf67880a701dca4683564f2cd24be4b2451161db438854` |
| `NativeCyclicCarryWord.lean` | `137fc02188a5f61dbbdc2bb65ac6a11017c5a182ec3d62d94e3d0191d8ad9fe8` |
| `NativeCyclicCarryWordAudit.lean` | `63f82882246ce1d9b7daa6f310ca145c3604e42a9a35e86b84a5d7accb1fe5af` |

The carry update is a monotone map on the bounded function lattice with
values in `Fin (D+1)`. The strict budget
`raw i + D < (D+1)*rho` proves it maps that box into itself. A fixed point
therefore supplies the actual simultaneous quotient recurrence. No
starting carry is fixed to zero and no uniqueness is assumed. The theorem
works for arbitrary predecessor maps, including the cyclic predecessor.
Quotient/remainder arithmetic gives the exact local digit identity. A
strict local bound resets its outgoing carry; a predecessor reset removes
only the incoming carry at the next field.

For the actual cyclic predecessor `i-1`, multiplication by the radix
rotates the carry word modulo `rho^n-1`. Summing the local identities and
cancelling that congruence proves the raw and normalized words congruent.
Normalized digits imply their word is at most the modulus. The assumptions
`0<F<rho^n-1` exclude its all-maximum-digit endpoint and give equality to
F. No stronger per-digit slack hypothesis is inserted. The convolution
wrapper uses the actual existing product/convolution congruence. The mask
wrapper uses the existing power-of-two digit-mask equivalence.

The radix47/carry57 specialization has the explicit raw envelope
`56*2^47+2^46+1930942`. This agrees with the integer form of the bound in
`research/padding-staircase-independent/PROOF.md`, lines387-412:
the doubled coefficient sum is below `56*rho+1930940`, there are three
Boolean units, and the temporal term is at most `rho/2`. The new Lean
specialization proves the envelope implies the carry box; it does not
yet prove that envelope from the literal native coefficients.

ROOT freshly ran both main modules with `lake env lean ... -o ...`, and
both corresponding audit modules with `lake env lean ...`, successfully.
The author separately lake-built all four. Audited theorem dependencies
contain only standard `propext`, `Classical.choice`, `Quot.sound` (some
local lemmas need only `propext`); no `sorryAx` or new axiom appears.
This uses the prepared pinned dependency environment documented in the
Carrier65 arithmetic review, rather than a claimed full-repository replay.

The checks exhibit genuine last-to-first carry, the distinction between
incoming and outgoing reset, raw word2009 normalizing to11 modulo999,+a one-field cyclic word, and the exceptional all-maximum/zero residue.
The final example proves why positivity of F cannot be silently omitted.

The literal current kernel, support and mass bounds, complete transport
and mask bindings, staircase, phase, tile-language soundness and canonical
completeness remain required. This checkpoint proves their bounded-carry
arithmetic prerequisite, not the final Con(ZFC) equivalence. It changes no
maintained equation, coefficient port, rendered page or ordinary packet.
