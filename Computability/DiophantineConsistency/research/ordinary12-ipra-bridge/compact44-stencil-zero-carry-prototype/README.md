# Boolean zero carry for the compact stencil mass

`CompactStencilZeroCarry.lean` identifies the model coefficient sum of the
two aligned bands, bare rotations and added temporal term with the checked
finite `stencilMass`. It proves `stencilMass + 1 ≤ 2^67 - 1` and applies the
generic Boolean zero-carry theorem. Thus, for an existing heterogeneous
carry input with these concrete coefficients, if **every** source word has
Boolean radix-`2^67` digits, every cyclic carry vanishes and every output
digit equals the raw column sum.

The theorem still assumes Booleanity for the entire source family, including
the temporal word. It does not yet identify the raw-column output with the
physical `blk` cells, prove high-mask no-carry, a graph zero or an internal
iPRA proof.

The first bounded attempt failed at a cast-over-finite-sum simplification;
its source and compiler output are retained in `observations/attempt01`.
The corrected single-author run, tool session `74534`, exited 0 without
warnings or `sorryAx`; the three axiom reports list only `propext`,
`Classical.choice`, and `Quot.sound`. Source/object hashes, direct dependency
and companion guards, command, dependency listing and compiler output are
in `observations/attempt02`; the guards were unchanged. The earlier provider's
package, transitive, dynamic-loading and between-observation ancestry remain
inherited; this is not a paired replay or a fully authenticated closure.
