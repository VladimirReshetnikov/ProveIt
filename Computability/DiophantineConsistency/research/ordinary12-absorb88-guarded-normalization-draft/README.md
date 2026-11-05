# Guarded normalization from an 88 zero to an 89 zero

`exists_89_of_normalization_guard` is a checked Lean theorem in the
indicated models of IΣ₁. It starts with an actual positive 88-graph zero at
ports `p`, with `beta>0`. Write

```
b=J*beta, q=1+b, A=K0+w, D=q*(q*A+1),
Bp=q*A, Bn=(F+alpha)*A+F.
```

It additionally assumes model elements `j,u,Fnew,anew,t` satisfying the
**explicit guard**

```
0<Fnew, 0<anew, 0<t,
F     = Fnew + b*j,
alpha = anew + b*b*j,
D*j   = u+t,
ιq * (ιBn−ιBp) = ιb * ιu.
```

The last equality is in the model difference ring; the others are equations
and inequalities in the natural-number model. Under these hypotheses it
constructs a positive zero of the 89 graph **at the same ports**. It replaces
`F,alpha` by `Fnew,anew`, respectively, and replaces the independent first
root witness using the first Pell root and `t`; the actual main and ordinary
factors are preserved by the checked [ring identities](RING.md). The new
transport is positive, after which the previously checked conditional
88→89 theorem applies.

The theorem does **not** prove that every negative-transport 88 zero has
guard witnesses. Its guard may fail for individual partial-factor examples;
the other graph factors must still be used to establish it or a different
normalization. Consequently, this is not unrestricted 88→89 existence or
an iPRA endpoint. The source's `Draft` comment predates the successful check.

## Observed check

On 2026-11-04 Lean 4.32.0 exited 0; the theorem reported axioms
`[propext, Classical.choice, Quot.sound]`, with no `sorryAx` or warnings.
The direct ring-stage input was checked separately with numerous unused
simp-argument warnings as recorded in [RING.md](RING.md). From the
repository root with prior captured objects available:

```sh
TASK_LEAN_PATH=$(python3 -c 'import json; print(json.load(open("Computability/DiophantineConsistency/research/ordinary12-absorb88-probe/observations/conditional-attempt01/result.json"))["lean_path"])')
LEAN_PATH=/tmp:/tmp/absorb89-chain-gpc9zymd/lib:$TASK_LEAN_PATH \
  /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/ordinary12-absorb88-guarded-normalization-draft \
  Computability/DiophantineConsistency/research/ordinary12-absorb88-guarded-normalization-draft/Absorb88GuardedNormalization.lean \
  -o /tmp/Absorb88GuardedNormalization.olean
```

Source SHA-256:
`28872ab12399f555f13c6fced5cb14273594643eb4396a9b12dd8882a7773db6`;
output SHA-256:
`e567a603c9050a2f723df136e72b7a710ccf4f8e06769da85ce42745b8a5700f`.
Direct local input hashes:

```text
Absorb88NormalizationRing.olean e9864486b2ed0ed7478b6367405458df92c80f5cb36da9976202ef75058a2bc7
Absorb88MainRoot.olean          f5c725deeddd1fcad2faf31a607e34307547ac9f7c4d4de9c2f61552617eab40
Absorb88Conditional.olean       eb29868c7558f0c5de32b47f5ef926a62890d0dda0be034881dbf1a13100ddb2
```

Temporary provider transitive source/object, package, dynamic-library and
search-path ancestry was inherited and not independently audited.
