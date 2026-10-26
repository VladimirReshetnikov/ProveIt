# Independent review of the reverse-discovery decimal seed

Result: PASS for the exact finite representation change described below. I
read the entire new proof and auditor, read the entire inert source packing
lemma, ran the auditor normally and with `python -O`, and independently
reconstructed the decoding and complete integer ports without importing the
auditor. I found no gap in the claimed identity. This review does not assert a
smaller complete printed page: the new numeral needs a different decoder.

## Frozen inputs reviewed

All paths below are relative to `Computability/DiophantineConsistency/`.

| File | SHA-256 |
| --- | --- |
| `research/reverse-discovery-decimal-seed/PROOF.md` | `7ae325c52d69c718266aee8ec116a29ca50353cf3edf20bd15c3abf73f0286c0` |
| `research/reverse-discovery-decimal-seed/audit.py` | `5e1ccfd248d1d521f8a847a37d74468252dd896e8025164e9fd4b699c9948bb9` |
| `research/reverse-discovery-decimal-seed/CERTIFICATE.json` | `87c1cc8d349b0472e4917ab9517cb7b907db0d34ce877d321331976cace161af` |
| `research/reverse-discovery-decimal-seed/DECIMAL_INTEGER.txt` | `313907d4b38e5d620d85b66f849368960d796ca6e442a8ee6b396c7d67d5a8a7` |
| `research/reverse-discovery-decimal-seed/OLD_DECIMAL_INTEGER.txt` | `bb8a7c133fe5baafbb41a8b7c1cbadce613e4dc8e79b6866313254dd07bea514` |
| `con-zfc-diophantine-forms/183-pell-carrier65/proofs/SEED_PROOF.md` | `c709c60d1b4e3ab504cb1cf1b3c9385cb95b7a364e1b08eabdc5f0dab1f60634` |
| `con-zfc-diophantine-forms/183-pell-carrier65/equation.tex` | `9e72ea21099e68bb095e3651c94c2725493f92c3aafc9d76c0ce7d914ee56582` |

The last two files were read as inert text. The former incoming archive is
historical provenance; this review does not claim to have rerun that archive
or any submitted program. No incoming program or TeX was executed.

## Packing lemma and the actual decoder

The prefix-product proof is valid even when a discovery has radix one.
For every prefix, its weighted digit sum lies in `[0,P_j)`. Consequently the
lower prefix cannot affect the quotient digit at position `j`, and every
higher term is divisible by `P_j r_j`. Appending `P_m E` therefore preserves
every target digit and makes the final quotient exactly `E`.

The target expression uses `sigma_(j+1)`, so it gives the newly discovered
state when the digit and radix are zero and one. For an old state it gives
the state itself. For halt it gives `-1 mod 216 = 215`. The outer modulo is
essential on the actual data: action 125 has `sigma_125=80`, radix 82,
digit 81, and target 215. Omitting the modulo changes that action.

The discovery mask and exceptional-flag mask fit the unchanged 636-bit low
field. Radices depend only on that mask, so the definition is not circular.
The flag quotient and its increasing-state nibble order agree with the old
encoding. There are 214 radix-one actions and 71 exceptional nibbles.

The auditor constructs the new integer from the old authenticated actions
before comparing it with the inert source numeral. It also reconstructs the
entire old base216 integer from those actions. The two new decoding routes
compare every returned action, discovery bit, prefix count, digit, flag and
packed flag integer; the comparison is not a checksum of a partial trace.
Actual first-, middle- and last-digit numeral mutations are checked, as is
the actual halt-modulo omission. Explicit exception checks remain active
under optimization. The default invocation compares the complete
deterministic artifact bytes; only `--write` regenerates them.

## Independent arithmetic reconstruction

Besides the two successful read-only auditor runs, I used a separate inline
Python calculation without importing the auditor or its model functions.
It decoded all 430 old target/write/direction triples directly from the old
decimal integer, formed all 431 prefix products directly from the resulting
radices, decoded the new numeral and checked every prefix bound. It
reconstructed the full identity

    A_new = N + 2^636 (sum_j d_j P_j + P_430 E)

and compared every action with the saved full data. The result was equality
for all 430 actions and all 431 prefix endpoints, including the radix-one
and early-halt cases.

I also independently rebuilt all 3297 doubled coefficients algebraically
from each complete saved tile table and the 34 label coefficients. I then
formed the entire `beta`, `K`, `MC`, and `MF_source` integers by direct sums
for both the scaled2953 and reversed2521 layouts. All arrays and all eight
whole-integer hashes matched their receipts. Coincident kernel terms were
added, including the reflected coefficient and the unit marker term.
The zero-weight dummy and marker remain physical mask positions.

## Scope of the conclusion

The new integer has 2373 bits and 715 decimal digits; the old integer has
2594 bits and 781 decimal digits. This is a saving of 66 numeral digits.
The complete actions, both 942-tile layouts, both complete coefficient
arrays and every whole integer port are unchanged. Thus the respective
specialized P66 and Carrier65 polynomials are literally unchanged, and
their already established ordinary proof contracts transfer by equality.
The whole-port byte totals remain 69449 at2953 and 59297 at2521.

This packet proves an exact finite identity. It does not newly establish
the machine calibration, consistency, formal end-to-end replay, a smaller
arithmetic graph, or global minimality. A complete new page still requires
its own source binding, decoder comparison, rendering and size review.
