# Square-shell recoding supplement

These four source files are unmodified extracts from the pinned incoming
`ConZFC_Shared_Residue_Bounds_2026-10-25.zip` archive. Their exact archive
paths, byte counts, SHA-256 hashes, and repository pin are in `PROVENANCE.json`.
The constructor hashes also agree with the inherited `constructor_sources/SHA256.json`.
The immediate Joint Norm parent remains unmodified in its own directory.

The delivered direct polynomial uses the `xx0` square-shell encoding. The
parent raw source labels its variant
`factorial_carrier_reciprocal_prime_power_xx0:signed_pooled_cap:shared_centered_remainders:odd_multiplier_and_normalized_rounded_ceiling`.
Its constructors are

    I(x,y)=2((x+y)^2+x),           M(x,y)=I(x,y)+1,
    A(x,y)=2((x+y)^2+3x+4y+3),    E(x,y)=A(x,y)+1.

They differ numerically from the older Cantor constructors printed in the
retained `calculus.tex` and `direct_calculus.py` files. Those earlier files
must not be read as literal definitions of the final arithmetic circuit.

`SHELL_ENCODING_PROOF.md` supplies the required unbounded logical bridge:
there is a constructor-preserving recursive bijection between the Cantor
and square-shell codes, fixing truth 0 and falsity 1. It transports every
C222 rule and preserves the guarded bundle's disequalities. The arithmetic
freshness witness d is reconstructed from the new labels; it is not
transported by an invalid assertion that the coding map preserves addition.
Thus a finite refutation in the square-shell calculus is equivalent to a
finite refutation in the original calibrated C222 calculus.

The constructor source and derived-label source authenticate the concrete
formulas and the expression used as the global semantic Pell anchor. They
are preserved source excerpts with their original imports; they are not a
standalone replacement for the entire historical compiler. The release's
new transformations start from the complete literal parent polynomial.

This supplement closes the explicit ordinary recoding dependency. It is not
a claim that the full Lean dependency tree was copied or recompiled.
