# Fixed PAeq suppliers for normalized identity packets

`NormalizedIdentityPacket param` requires a valid arity-zero packet, the identity free-variable environment, and result code `^&0`. In every model of IΣ₁, `normalizedIdentityPacket_exists L` constructs one of any model-valued length `L`. The last condition is stronger than `IdentityPacket` in `pa194-guarded-compiler`; the packet constructed by that module's `identityPacket_exists` already has the normalized result.

The existing model-uniform typed quotation theorem applies to a normalized identity packet. The five fixed PAeq propositions already supplied to the source theory—reflexivity, zero-not-successor, addition-zero, multiplication-zero, and symmetry—have no free variables, so their typed translations under the identity and constant free-variable environments are definitionally equal. The five `identity_*_provable` theorems therefore prove the exact dispatcher image of each universally closed fixed axiom in the full source theory, for every candidate PRA + IΣ₁ model, any normalized identity packet, and the displayed packet-length bound.

This does not establish environment independence for arbitrary internal formula codes, the full guarded theory-axiom rule, the induction supplier, the nonvariable existential rule, or an iPRA implication. To use these theorems in the guarded endpoint, its `hrules` quantification can be specialized to normalized identity packets, since the packet existence theorem supplies them.

Reproduce from the repository root with a fresh empty output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-identity-fixed.sh "$PWD" /dev/shm/pa194-identity-fixed-repo-NEW
```

The checker rebuilds two source modules and an eight-report audit, using the separately replayed fixed-axiom source suppliers and the other prebuilt paths listed in the checker. It does not rebuild the full import closure.
