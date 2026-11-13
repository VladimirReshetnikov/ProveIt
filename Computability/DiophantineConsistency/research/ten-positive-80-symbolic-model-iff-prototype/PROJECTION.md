# Four symbolic port equalities

`Direct80SymbolicPortProjection.symbolic_iff_of_four_ports` discharges the
integer-tuple equality and second-port model-cast hypotheses of the conditional
iff. The remaining assumptions are the four natural port equalities
`p 0 = betaNat`, `p 1 = paramKernel rho`, `p 2 = lowNat`, and
`p 3 = betaNat + highNat`. A generic four-coordinate extensionality lemma
avoids expanding the fixed coefficients when constructing the tuple equality.
The conclusion is a positive graph zero iff the represented machine halts, in
every supported IΣ₁ model. It does not establish external file binding or an
internal iPRA proof and does not identify the distinct retained 80 K0 with
`paramKernel rho`.

The accepted check is `observations/projection-attempt01/`; the output
`/tmp/direct80-port-projection-m2n2gqa7/SymbolicPortProjection.olean` has
SHA-256 `b29a920b26eaa4ee347d9471a4a32bf38785883719826ceaa3246f37b4ae8809`.
Source SHA-256 is `cdd1b9831af2073d6f4c191fd5915a35014cc0d8a6b1c9f6fa803f177133fdf8`;
runner SHA-256 is `1a4eed8e73fd53d774a32c4bb44d19f0b5f34a4a16cd15a7671ead2709b4381b`.
The runner pins the selected direct import before and after Lean and records
resource samples. No `sorryAx` is reported; the source/object, package and
dynamic ancestry limits of the imported provider remain inherited.
