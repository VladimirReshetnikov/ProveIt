# Independent review of the complemented-receiver native tuple

The source is `docs/incoming/con-zfc-selective-2026-10-23.zip` at
ProveIt commit `4b4349064a750ba6347293b55874a7f92abdd0db`. Its exact archive
Git blob is `143a1487c8c28aac7e14c6e723a763040c508d0b`. The proof and literal
data are under `sources/con-zfc-selective-2026-10-23/con-zfc-selective/coefficient_adapter/`.
No upstream program was imported or executed.

## Result

The independently reconstructed four-port tuple matches the supplied bytes
exactly. Its base is `B=2^429959`, using radix `rho=2^89` and cell length
4831. Its four raw payloads occupy 215492 bytes. The prior complete tuple
used by round 7 occupies 295388 bytes, so the reduction is 79896 bytes,
approximately 27.05 percent. This is a coefficient-height improvement;
neither the variable count nor the arithmetic graph changes solely by
rebinding these ports.

The materialized ports are under `../native/`. Every compatible rebinding
must replace all four ports and regenerate derived coefficient leaves.
`MF_source` already equals `MF_native+B-1`; shifting it again is incorrect.

## Universal decoder review

The claimed local decoder is valid on inspection. Let `n` be the number
of selected modes, `T=2^42`, and `M=4T`. The low nine-bit mask forces
`n` to be zero or one before reasoning about higher fields. The next
three gated fields have no overflow after this restriction. They force
the inactive directional receiver payloads to vanish whenever `n=1`.

Let `Z` be the copied 42-bit label word, `y` its west least-significant
bit, and `A1,A2` the standalone anchors. The aggregate word is
`W=Z+T(y+A1+A2)`. Horizontal labels are doubled, so the uncomplemented
label sum and all auxiliary increments `V` are even. The aggregate
congruence modulo two forces `y=n`.

If `n=0`, then `y=0`, `V<T` and `W<3T`. The enforced congruence
`V+W=0 mod 4T` therefore gives `V+W=0` as an equality. Since all summands
are nonnegative and each payload bit has a positive coefficient, every
payload, copied bit and anchor vanishes. The two ignored dummy digits
are the only exception. This closes the earlier factorized-receiver
empty-cell gap without presupposing alignment.

If `n=1`, the gated label sum `L+V` lies in `[0,T)` and the aggregate
sum is strictly between zero and `2M`. Its zero residue therefore means
`1+L+V+W=M`. Hence `W=3T+(T-1-L-V)`. All three anchor bits are one and
the low word is exactly the fieldwise complemented labels. Horizontal
complemented low bits are one, consistent with the reused west anchor.
The converse is immediate by substitution.

## Synchronization and semantic interface

The finite support conditions are independently checked modulo the entire
native cell, not only on an unwrapped interval. The two clause supports
are disjoint, while the two temporal anchor supports intersect only at
zero. At the forced Start cell a clean clause gives both anchors one.
The inherited parity estimate excludes every nonzero bit rotation; the
single exceptional upper-dummy spill cannot serve both targets. The
support intersection then excludes every nonzero cell-position rotation.

After alignment, the local theorem gives an empty cell only when its
west copied parity is zero. An occupied east parity is one, and spatial
matching propagates occupancy from Start throughout the cyclic word.
Complementation and doubling preserve label matching injectively. The
expanded language reduces exactly to the original admissible 942 tiles
after discarding 536 impossible receiver tiles and the forbidden tile.

The completeness controller is also consistent: the prime 106261,
the exact order 26565 modulo `89*4831`, the non-Wieferich lift modulo the
prime square, all controller unit residues, and the Boolean rank-control
inputs pass exact arithmetic checks. The source's subset-sum argument is
the inherited controller lemma with these verified inputs. The proof
retains its unbounded marked-Wang, native-window/Pell and K215/refutation
dependencies. This review does not replace them with finite testing or
claim a new proof-assistant certificate.

## Independently checked finite data

`check_separated_tuple.py` and `SEPARATED_TUPLE_CHECKS.json` record:

- 430 transition actions, 457 selector modes and 520 native support positions.
- 37960 scalar basis identities and both modulo-cell support conditions.
- 1479 occupied decodings and 65076 single physical-bit rejection checks.
- All 131072 empty receiver payload possibilities, with exactly the zero
  payload representable by the parity-linked anchor word.
- 537 unmatched expanded tiles, leaving the exact 942 admissible tiles.
- Uniform carry mass, mask populations, low congruences and padding bounds.
- Exact reconstruction and SHA-256 authentication of all four raw payloads.
- The three primality checks, exact multiplicative order, lift and unit table.

No discrepancy was found. These are finite checks plus an ordinary proof
review, not a consistency test and not external human peer review.
