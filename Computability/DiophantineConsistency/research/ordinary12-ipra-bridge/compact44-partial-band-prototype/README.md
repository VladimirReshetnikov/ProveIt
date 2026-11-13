# Conditional reflected-band column identity

`CompactPartialBand.band_decomposition` proves a local model identity for one
finite reflected selector/copy band. The word length `n` is an element of an
arbitrary IΣ₁ model; the selector index type `Fin 943`, copy index type `Fin 41`,
standard target `T` and copy-position map are external finite data. Under the
explicit assumptions `0<n`, `k<n` and `C<Exp.exp (67*n)`, it rewrites the
digit of each **radix-aligned** reflected rotation using `dig_rot` and
`cyc_mod`, then applies the existing finite coefficient decomposition. Thus
the weighted sum of those rotation digits equals the local decoder expression
for the corresponding source digits.

The theorem handles only the selected band, with offsets written using the
displayed natural subtractions; it does not prove any target/position bound
needed to interpret those subtractions in a particular recipe. It does not
identify this band with the full graph column, prove other contributions
vanish, interpret the graph's temporal factor as an aligned rotation, derive
any no-carry or Boolean premises, bind retained K bytes, simulate a machine,
or establish an iPRA endpoint.

Exploratory session 7611 actually exited 0 without warnings. The named
declaration reports `[propext, Classical.choice, Quot.sound]`. The run used the
author side of the paired coefficient-decomposition provider; it is not a
paired rebuild of this client and inherits the parent/provider qualifications.
The exact command and observed output are in `observation.txt`.
