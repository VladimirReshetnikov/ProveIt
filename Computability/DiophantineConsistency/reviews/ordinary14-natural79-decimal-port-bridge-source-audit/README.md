# Source audit: proving the four natural-79 decimal port equalities

The [port bridge draft](../../research/ordinary14-natural79-decimal-render-candidate/Natural79DecimalPortBridge.lean.src)
assumes four equalities of **Lean natural numbers**, then proposes substituting
them to obtain the native-iPRA endpoint for the same 79 graph. Its target is
`nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding`, as a formula
provable in `nativeTheory`. This bounded audit identifies existing source
interfaces and remaining work; it does not elaborate the draft or authenticate
its imported objects. The four equalities themselves are ordinary external
Lean arithmetic claims and do not inherently require additional arbitrary-model
lemmas. Their use does require the separately unelaborated natural-79 endpoint.

The tuple expected by `CompactSymbolicModelIff.p` is exactly
`[betaNat, paramKernel rho, lowNat, betaNat + highNat]`, cast componentwise
from `ℕ` to `ℤ`. The draft's four parameters and assumptions match those
positions at source level. The high component is already shifted; adding beta
again would change the equation. There is no `positiveShift` in this 79 bridge:
its 14 inputs are nonnegative; the historical Carrier65 positive-input quote is
a distinct syntax and port instance.

A lean **direct symbolic route** needs the following concrete definitions and
proofs; none is supplied as a theorem in the bridge:

1. Define the page's `βd = (2^67)^8807 - 1`. Rewrite
   `CompactFixedBeta.betaNat = 2^(67*8807)-1` using the natural power-of-power
   identity. Preserve natural subtraction until the bases are rewritten; avoid
   expanding the 590,069-bit numeral.
2. Define an actual Lean natural `P` from the printed 15,086 decimal digits.
   Let `B=10^16` and `L = Compact943Data.rows.map CompactCoefficientMass.selector`,
   in source order. Prove the essential missing finite identity
   `P = Nat.ofDigits B L`. `Nat.ofDigits` uses least-significant blocks first;
   the printed integer has 943 blocks and therefore two leading zero digits when
   padded to 15,088 digits. Prove each selector is `< B`: the source's
   `values_in_range`, its selector definition, and a finite numerical bound are
   usable ingredients. Then `SparseRadix.digit_ofDigits`, `rows_length`, and
   the `Compact943Data.row` indexing definition give the page's
   `(P / B^j) % B = selector (row j)` for each `j : Fin 943`. This one block
   theorem can replace 943 separate giant decimal divisions. The equality of
   the **literal** decimal P to this block construction is still a real finite
   proof obligation; defining P only as `Nat.ofDigits B L` would not by itself
   connect it to the printed digits.
3. Define the page's K as its displayed sums. Use the block theorem above,
   `CompactSymbolicKernel.position`/`slots_length` for the 41 copy positions,
   `CompactSymbolicKernelOpaque.paramKernel`, `rho = 2^67`, finite-sum index
   conversion and `ρ^8807 * ρ^42 = ρ^8849`. Index bounds matter for natural
   subtraction in `4393-j`, `5495-j`, and the slot exponents. The source has
   `row_lt_target`, `slots_bounded` and `position_lt_target`; their applicability
   must be checked in the selected environment.
4. Define the page's μ using its support and extra defect. After unfolding
   `CompactSymbolicPorts.lowNat`, `CompactConcreteMask.concrete_recipe` has
   exactly the needed symbolic mask identity, with support membership and the
   special index already built into that theorem. Establish that the page's
   support notation is the same `Finset` and reuse the beta equality; do not
   replace `Nat` subtraction by ring subtraction without the required bounds.
5. Define the page's `H` and `ω = βd + H`. Unfold `highNat` to
   `Nat.ofDigits (2^67) CompactHighPopulation.highDigits`; prove that the
   run-length list decodes to the displayed finite sums. Existing
   `ArithmeticMaskData.ofDigits_replicate_append` and its geometric-sum lemmas,
   together with `Nat.ofDigits` append rules and the high-digit definitions,
   are a plausible non-expanding route. The high list is little-endian. Then
   use the beta identity to obtain `ω = betaNat + highNat` with one shift.

The **byte-recipe route** can instead use
`CompactFourPortByteAssembly2.decode_ports`, which states that decoding four
closed Lean byte-list recipes in base 256 equals the symbolic tuple. Its
`CompactBytePortsModelIff.byteP_eq` companion casts the tuple to integers. This
can avoid reproving parts of the symbolic byte machinery if one proves that the
four page-defined naturals equal the corresponding decoded Lean recipes. It
does **not** supply those decimal-to-recipe equalities and does not read or
prove anything about gzip, JSON, TeX or PDF files. The prior external byte
comparison and this source audit cannot replace that Lean link. Importing this
route also adds its own provider and axiom-closure obligations; presence of a
historical `.olean` alone is not authentication in the future build context.

After the four equalities, the port bridge still needs to elaborate its
substitution and tuple simplification. Existing endpoint modules deliberately
mark large constants locally irreducible; protecting the same constants or
using a focused componentwise tuple equality may avoid accidental huge
normalization. The decimal P comparison may likewise need chunked certificates
rather than one monolithic `decide`; the available resource limits must be
sampled and enforced before any build. These are implementation risks, not
claims that any suggested proof script succeeds.

The bridge constructs `P79NaturalForcedW.graph` directly. A full claim about
the displayed equation still needs a Lean definition of the displayed 79-row
abbreviations and a proof that it denotes that expression, plus the intended
natural split-zero/integer-evaluation correspondence (the source offers
`ModelDifferenceRing.internalZero_iff` in an appropriate model). A formal
claim about actual TeX or PDF bytes further needs a verified interpretation or
parser; source/PDF hashes and the independent external rendering check do not
supply one. No theorem of either side, no Lean axiom report, and no iPRA
end-to-end result is established by this packet.

The checker pins the inspected interfaces and verifies the relevant literal
source declarations. It does not run Lean, test a proof tactic or survey full
compiled ancestry. From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-decimal-port-bridge-source-audit/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-decimal-port-bridge-source-audit/result.json
```
