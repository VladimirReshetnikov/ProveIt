# Checked compact54 local native decoder

`NativeSelectorClause54.native_clause_iff` proves exact local acceptance for
the actual457 compact54 selector modes. Its input is an arbitrary Boolean
selector vector, the two receiver bytes, common payload bit,42-bit copied
label word and two Boolean anchors. No one-hot selector hypothesis, accepted
tile hypothesis or native-correctness hypothesis is supplied.

The accepted states are exactly:

1. all selectors, receiver payloads, copied labels and anchors zero; or
2. one selector, its allowed receiver payload, copied labels equal to the
   fieldwise complement of its expanded tile, and both anchors one.

`anchors_eq_selectorCount` further proves that both standalone anchors and
the copied west parity bit equal the cell's occupation bit. Ignored dummy
digits have zero clause coefficients and are not inputs to this local test.

The exact clause mask is

```
510 + 2^17 + 2^26 + 2^28 + 2^29*(2^44−1).
```

The low selector field is decoded first, without a carry assumption on the
higher fields. Every selector coefficient is1 modulo512, while all auxiliary
and copied-label coefficients vanish modulo512. Boolean457-selector inputs
give a count below512. The low mask then forces count zero or one. Only
afterward do the three receiver gate fields fit their9,9,2-bit widths,
allowing the higher masked fields to be decoded independently.

The aggregate proof uses the literal positive receiver increments and
`T=2^42`. Its44-bit congruence forces an empty cell's complete payload to
vanish, excluding nonzero payload in an unoccupied cell. In an occupied cell
it forces both standalone anchors and the copied west parity bit to one,
and the copied label word to `T−1−expandedLabel`. The two horizontal label
fields are doubled, matching the authoritative compact54 recipe.

The seven public mode-based theorems in `NativeClauseModes54` prove the field
ranges and the local equivalence for an ordinary mode or the actual receiver
bases `(256,0,0,512)` and `(0,0,512,512)`. `NativeModesData54` instantiates
these hypotheses for all457 literal modes, including receiver indices374
and4, Start at0 and the forbidden mode at1.

`generate_native_modes54.py --check` reproduces the table from the inert
430-transition export whose SHA256 is
`880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755`.
This is the identical transition file in package36 and the authoritative
package54 archive at source pin `4b4349064a750ba6347293b55874a7f92abdd0db`.
The declarative tile families and mode ordering match package54's
`native/verify_native_tuple.py`. The finite Lean checks prove the table's
length, receiver bases and all ordinary10-bit label bounds; they do not
prove that its JSON transition source equals the current Lean machine table.

`NativeLocalCoefficients54.coefficient_word_eq` proves the actual positive
selector, receiver and copied-label recipes evaluate to the packed clause.
`NativeClauseBits54` proves their individual eight-bit receiver and42-bit
copy coefficient sums equal those aggregate words. The west low copied bit
is included once in its label and once in the shared anchor field, exactly
as the coefficient at native position539.

All six modules have dedicated public-theorem axiom checks, with no axioms
beyond `propext`, `Classical.choice` and `Quot.sound`. The mode table's
length/membership facts need no axioms, and several coefficient identities
use only `propext`.

The remaining global soundness contract is to derive isolated local clauses
from `NativeSourceWindow` for the whole fixed native tuple. This requires
the current/spatial convolution identities, the no-carry mass bound,
clean-band selection and temporal phase synchronization. One must then
extract a marked matching tiling and prove its K215 run interpretation.
Canonical tiling/padding and Pell witnesses are also needed for the reverse
direction. The local decoder closes none of those global obligations by
assumption, and asserts no internal ZFC consistency biconditional.
