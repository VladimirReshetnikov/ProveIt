# P65 iPRA endpoints through an alternate captured-provider assembly

`P65UnconditionalEndpointDraft` proves the `ReverseDirection` hypothesis of
`P65IPRAHaltReverseAdapter` by applying the separately replayed
`P65Facts.halts`. Applying the checked conditional adapter then yields native,
standard and equality-only iPRA equivalences, with no extra theorem
hypotheses. Each states that the shifted fixed-port P65 Lean graph has no
natural zero iff the corresponding mapped Foundation ZFC refutation sentence
is false. `positiveShift` maps natural valuations to positive valuations of the
original graph.

The expression is `(P65Graph.graph
(CompactSymbolicPortProjections.portsInt (paramKernel rho))).output`, the
same expression stated in the merged canonical `IPRAPositive65.lean` (source
SHA-256 `675eafadc49f1248e80a965d834b702d073eafda4c0aff5f0cc84f1fb1c9d7f1`).
This packet combines an alternate halt-side construction with a replay of the
reverse theorem; it is **not** an independent clean build of the merged
canonical endpoint or all its dependencies. The baseline provider and
source/object ancestry limitations in `research/p65-reverse-provider/` and
`research/p65-canonical-data-binding/` remain. Finite correspondence to any
external JSON, TeX or PDF requires its own check.

Lean 4.32.0 checked the frozen source in actual sessions 76063 and 50405, exit 0 and no
warnings. `#print axioms` reports `[propext, Classical.choice, Quot.sound]`
for the reverse theorem and each of the three endpoints. The first attempt
was rejected due to an ambiguous short name `expression`; the frozen source
uses the fully qualified name.

```sh
LEAN_PATH=/tmp/p65-reverse-provider/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 lean -M3000 -j1 -DElab.async=false \
  --root=research/p65-unconditional-ipra-alternate-provider \
  research/p65-unconditional-ipra-alternate-provider/P65UnconditionalEndpointDraft.lean \
  -o /tmp/P65UnconditionalEndpointFrozen.olean
```

```text
P65UnconditionalEndpointDraft.lean  1d7fde35e4c85864d6d883151b07d541a74f585168b9cbddeff95b0f5fe87a23
P65UnconditionalEndpointFrozen.olean d6b7683850bcf07135eb345ef863469f8672bb64b0ba8de7e58a7e4fb56ff498
replayed P65Facts.olean             cbb4b53c2ce1c4ce6ea56a5efcd04223faff5e714160694d337baa9daeaac5ae
lean-check.log                      24e8ba8ca3ae40a19c311ec4e1244c3d8afe67c986cabb879bf5137f6bcf3cc8
```
