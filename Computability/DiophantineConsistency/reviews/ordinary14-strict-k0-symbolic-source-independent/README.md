# Independent review: symbolic K0 positivity draft

The [source draft](../../research/ordinary14-strict-k0-symbolic-source-draft/README.md) gives a mathematically sound route to strict positivity of the selected symbolic K0 port, conditional on the cited splitting and model-cast declarations. No extra hypothesis about beta or the other ports is needed for that local argument. Neither receipt runs Lean or connects this symbolic value to physical coefficient bytes.

The cited natural-number split states `paramKernel r = r^8849 + lowerKernelAt r`, with `lowerKernelAt r` itself natural. Since `rho=2^67>0`, the top term at `rho` is positive and the other term is nonnegative, so `paramKernel rho>0` as a natural number. In the intended arithmetic models, the draft applies `Nat.cast_pos` to carry that positivity to the model. The source of `ArithmeticMachineTape215` contains the same `Nat.cast_pos (α:=V)` pattern under the same `ORingStructure V` and `IΣ₁` model assumptions. This is supporting source evidence; the new application and inferred instances still need elaboration.

The tuple declaration puts its second parameter in slot 1, and the symbolic port tuple chooses `paramKernel rho` for that parameter. The draft proposes identifying the difference-ring cast of port 1 with the embedded model cast, then uses the cited `ι_lt_ι` order-embedding equivalence to transfer positivity. The representation's `change`, cast simplifications, the embedded zero rewrite and all instances are untested Lean proof steps. The split itself and its transitive providers are also not freshly replayed here.

The independent checker pins and inspects eight source files, including the split, slot tuple, model cast precedent and difference-ring order statement. Its finite natural computation checks the positive top term but is not a Lean model proof. The result does not establish symbolic-to-file equality, the forced-J graph transfer, axiom closure, or an iPRA endpoint.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-strict-k0-symbolic-source-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-strict-k0-symbolic-source-independent/result.json
```
