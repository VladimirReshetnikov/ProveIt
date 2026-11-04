# Height for first index 8 and main index 11

`Trace74N8R11HeightModel.tuple_height` proves in any model of `IΣ₁`
that a positive tuple with `q≥2³⁰` and **same-tuple** first and main
Pell ordinate equations at indices 8 and 11 satisfies

```text
33554432 · b · Y < X.
```

This coefficient is `8·(2¹¹)²`. The proof derives the strict Pell gap
from the positive offset and applies the width-three model Pell height
theorem to obtain `Y⁵<32X³`. The cubic bound `Y≥q³` and `b<q` then
amplify it to the displayed linear height. The intermediate theorem
`linear_height` retains all those numerical assumptions explicitly.

This does not require or assert a graph zero. It does not prove the
projection quotient obstruction, exclude the index pair, establish a guard,
or produce an iPRA endpoint. A separate graph client is needed.

Author check session 12345 exited 0, with `[propext, Classical.choice,
Quot.sound]` in each axiom report. Lean 4.32.0 was invoked with `timeout
120`, `-M3000 -j1 -DElab.async=false`, this directory as `--root`, and
`/tmp/Trace74N8R11HeightModel.olean` as output. `LEAN_PATH` was the
following captured provider sequence:

```text
/tmp
/tmp/trace74-graph-index-upper-sbqz0413/lib
/tmp/trace74-index-upper-lw94r446/lib
/tmp/trace74-index-order-vu44__7n/lib
/tmp/trace74-guardfree-residue-9rz_sl3r
/tmp/trace74-guardfree-offset-g91osrrh/lib
/tmp/trace74-odd-ordinate-bound-b8rmryeu/lib
/tmp/trace74-guardfree-fold-mqg70pbn/lib
/tmp/trace74-guardfree-adjacent-e85cpupi/lib
/tmp/trace74-guardfree-pell-jg0_m3mj
/tmp/trace74-arbitrary-root-wppvu6hp/lib
/tmp/trace74-direct-four-block-1zltaw2f/lib
/tmp/absorb89-chain-8h1sfgle/lib
/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib
```

```text
source        c86859699c81e6c7838b87921020daa434242732a4d207a0cd6e1f1827e8fce9
output        e2cea22621830b88f0939b38727332cf31dda2cf7f8423a7711e5485b907366d
Width3Pell    cd165fc9aa8dc39d2bc44f1b6a9c096c197c9065fe22b2d02b586ccda99c4110
PellGap       8ffc0282fa2dc540cbba08255c19ca780234da569fd2ad2b1163418c0966445a
```

One previous author check failed on fixed-numeral normalization. This is a
captured-provider check, not an independent replay or a coherent current
source rebuild; transitive provider and package ancestry were not audited.
