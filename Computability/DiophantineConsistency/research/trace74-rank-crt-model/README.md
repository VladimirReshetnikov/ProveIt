# Three-modulus rank-chart CRT in arithmetic models

`Trace74RankCRTModel.three_linear` proves over any commutative ring that,
for arbitrary signed targets `a,b`, the three simultaneous conditions

```text
D | U*z+a,   c | U*z+b,   h | W*z−1
```

have a solution when the three moduli are pairwise Bézout-coprime and
`U` is coprime to `D,c` while `W` is coprime to `h`. It uses explicit
ring CRT and linear inverses, without requiring a domain or positive moduli.

`positive_three_linear` transfers the construction to the difference
ring of any model of `IΣ₁` and constructs a **natural** solution `N`
above any supplied internal bound, with those three ring divisibilities.
The moduli are explicitly assumed positive and all six coprimality
certificates remain hypotheses. It shifts the ring solution by a multiple
of `D*c*h`, using the model's absolute-value/nonnegative decomposition.
The theorem does not yet supply the concrete rank-chart inputs, prove the
needed coprimalities, construct a 74 graph zero, or prove an iPRA endpoint.

Lean 4.32.0 was run with:

```text
LEAN_PATH=/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M3000 -j1 -DElab.async=false --root=Computability/DiophantineConsistency/research/trace74-rank-crt-model \
  Computability/DiophantineConsistency/research/trace74-rank-crt-model/Trace74RankCRTModel.lean \
  -o /tmp/Trace74RankCRTModel.olean
```

Actual session 3614 exited 0 without warnings. The all-ring report lists
only `[propext, Quot.sound]`; the model report lists only
`[propext, Classical.choice, Quot.sound]`. Source SHA-256:
`5da4236b73640a00c730f0a132002a44446c0e9caadb5a61542b0f30367df169`;
object SHA-256:
`f8d45fa06f4c40aae194890a996251ea5a6b76767a6dc221ad76bb972af29111`.
Direct `ArithmeticPow.olean` SHA-256
`2bc4bb37d326c0f77e3d7a40ff52133060c5cdb4fc6372f0f5308c3c2f284995`,
and `ModelDifferenceRing.olean` SHA-256
`d0fb8f9664675190dbfc25915a687cef203b8362681d9256606f1022a6dbde74`.
Two earlier attempts were rejected on missing imports/addition orientation
and then a nonnegativity elaboration, respectively. This is a
captured-provider author check, not an independent replay or a complete
current-source rebuild; transitive/package/dynamic/search-path ancestry
remains unauthenticated.
