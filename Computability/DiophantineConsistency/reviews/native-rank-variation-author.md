# Native rank variation: author receipt

Status: frozen, freshly checked. Author: `circuit_reduction`. This is an
author receipt, not an independent review. Only the new module, checks, and
this receipt were written; no existing sources, shared documents, or git
state were changed.

## Exact source binding

Paths are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/NativeRankVariation.lean` | 112 | `46c226eba0018eb15eaec66bb31b2ea8af7682fbef76d0245ee45c6aa236ef73` |
| `Lean/DiophantineConsistency/NativeRankVariationChecks.lean` | 77 | `a5d44d4819a48e3900e19ee2ad684015b4806dd5a661081203ac4c6dd95d6b0a` |
| `Lean/DiophantineConsistency/Carrier65.lean` | 256 | `be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154` |

Carrier65 is the sole direct import. Its entire source, including the exact
14-coordinate `core` definition, `rank_shape`, source-port convention, and
remaining theorems, was read before implementation. Both complete new sources
were read before their executions.

## Proven identities and precise assumptions

Over any commutative ring, the module defines

```text
windowRank q C F MC MF J = (q*(q-F)-C)*(q²-1)+(MC+q*MF)*J
rankGamma q A D = D*(q²-1)*(1+q*A).
```

`core_rank` proves that the actual Carrier65 rank is exactly this formula at
`q=core.q`, `C=core.C`, `F=v1`, `MC=p2`, `MF=p3`, and `J=v0`.
The proof uses `C=q-F-alpha` and the frozen literal `rank_shape`.
The MF argument is the existing source port with its one beta shift already
included; no extra shift or subtraction is introduced.

`rank_variation` proves the complete ordinary identity

```text
windowRank q (C+δ) (F+A*δ) MC MF J
  = windowRank q C F MC MF J - δ*(q²-1)*(1+q*A).
```

`rank_power_variation` specializes δ=D*B^j and factors the decrement as
`rankGamma q A D * B^j`. These are universal ring equalities with no
division, congruence, positivity, or nonzero hypotheses.

The actual-core adapters retain the same four ports and explicit equalities
for fixed q and J, new C, and new F. The latter is the ordinary equality
`v'1=v1+A*δ`, not a modular statement. The q equality is stated explicitly
alongside fixed J even though the same ports and J already determine q.
No existence, positivity, polynomial-zero preservation, mask preservation,
or carry-safety claim is made for such a modified front.

Over the integers, `rankGamma_pos` proves positive Gamma from q>1, A≥0, D>0.
`rank_strict_decrease` and its actual-core adapter prove strict decrease for
δ>0 under q>1 and A≥0. Neither the old/new ranks nor mask ports or window
entries need be positive. The symbolD here denotes a generic increment
coefficient, not Carrier65's independent Pell block called D.

At q=1, `rankGamma_one` and `rank_variation_one` prove the exact zero-step
control. No numerical controller, large K expansion, modulus order, CRT
orbit, or safe-increment construction is asserted by this packet.

## Focused checks

The checks retain the generic-ring difference identity and exact actual-port
binding. A second symbolic equality shows that adding beta to MF again would
change rank by q*beta*J. Concrete integer checks distinguish the full208 rank
drop from the incorrect16 drop that omits the F contribution.

The explicit congruence control takes q=3 and replaces the required new F=10
by13. Their residues modulo3 agree, but their ranks differ, so the ordinary
increment hypothesis cannot be replaced by that residue equality. This is an
algebraic control, not a purported native source solution.

Other checks cover position j=0, a nontrivial squared place value, q=1,
negativeA reversing Gamma's sign, and strict decrease with negative mask and
window arguments. No unconditional positivity or safe mutation is inferred.

## Fresh validation

Both new sources set `Elab.async false`. Sequential direct commands from the
repository root were:

```sh
/usr/bin/time -f 'elapsed=%e max_rss_kb=%M' lake env lean -M6000 -j1 \
  -o .lake/build/lib/lean/DiophantineConsistency/NativeRankVariation.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeRankVariation.lean
/usr/bin/time -f 'elapsed=%e max_rss_kb=%M' lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeRankVariationChecks.lean
```

Both passed on their first run. Main:3.14seconds, peak1985268KiB, no Lean
diagnostics. Checks:2.82seconds, peak1964276KiB, exactly ten intended axiom
reports. The ring identities/core adapters use only `propext`, `Quot.sound`;
the q=1 controls use `propext`; integer inequalities use the standard three
`propext`, `Classical.choice`, `Quot.sound`. No `sorry`, new axiom, or
`native_decide` was added. Existing prerequisites were reused; this was a
fresh check of the new packet, not a new replay of the full import closure.

| Output | SHA256 |
| --- | --- |
| `.lake/build/lib/lean/DiophantineConsistency/NativeRankVariation.olean` | `4d73da3692ddee9ed725396f830bf859743bcbfaaf5c90b6341007bd2f8c9232` |
| `/tmp/native-rank-variation-main.log` | `3e284174b156623a99fb963cac0a0b90b99a8d8ee67dc03c7c20c8b6a48e31b5` |
| `/tmp/native-rank-variation-checks.log` | `946e111647fba5ff4fb3f087fe43705532a7d832ffef1cef7939e044c3dcfe62` |
