# Independent review: actual2011 polynomial soundness for ZFC consistency

Date: 2026-10-26 UTC. Reviewer: `controller_certificate`. Result: **PASS**;
no correction requested to the frozen main or checks.

Root authored the reviewed composition. The reviewer authored important
earlier dependencies, including Carrier65, Carrier66 and its source map,
CurrentKernel2011, CurrentWindowCarry2011, CurrentPolynomialWindow2011,
CurrentMarkedWindow2011, and DecimalMachineZFC, as well as intermediate
label/translation/adjacency/occupation proofs and the actual Wang row step.
Root authored WangTiles942Soundness, independently reviewed immediately
before this packet. Circuit authored CurrentCarrierArithmetic2011; root
authored the literal mask and recipe modules. This is an independent
review of the new root composition and its exact bindings, not independent
authorship or a fresh-closure audit of every prerequisite.

Exact target and principal dependency bindings, relative to
`Lean/DiophantineConsistency/`:

| Source | SHA256 |
| --- | --- |
| `CurrentSoundness2011.lean` (72 lines) | `1118ee3f50dffa046e1205b72a8cac84ef02b5cad0862ef53b79cde1de4ba7ef` |
| `CurrentSoundness2011Checks.lean` (60 lines) | `5af7bd88072198d6ee68022792776aeb8e7104f5faabfc57f17306e41c69319f` |
| `CurrentMarkedWindow2011.lean` | `b8df6733e6a812d31e251c817076671ce319927fd635731af3e88bab309585d3` |
| `CurrentPolynomialWindow2011.lean` | `db64a1e9130d09d606f3262781be9a4c0d70db1a9cdb7482cd74ecc0ddf0b730` |
| `CurrentWindowCarry2011.lean` | `94f9ec318d90b66200757bba8992eb6560e283dbdceeac877e48eee80ade3d06` |
| `CurrentKernel2011.lean` | `6f8642d8d3715335dcf61fb0060818226f227db24e126d4c14d58831e76d3a55` |
| `CurrentMasks2011.lean` | `72ec99ac052c4d244f22f2590fb5645cebbe9ffe3a18fd89fe1cb8db7248fe06` |
| `CurrentMaskRecipes2011.lean` | `6dfe8ca1a8eaf16b74767cade35572d234d76ac22b409dc68f90cb87d904fbe3` |
| `CurrentCarrierArithmetic2011.lean` | `5f749fdfe0a3857c6d84b0505574f1b1d09f5b859167659a34b04ba392f4a5b3` |
| `ThirteenCarrier.lean` | `2f19e9690841d15d48a281cfafd8813270e0dcfe38a9f6c68ab9d2f9d85453ca` |
| `ThirteenCarrierSoundness.lean` | `50478151e2e94dcdf150838df7a60660ce93dfb57fb6bea03e0251e8801687ce` |
| `WangTiles942Soundness.lean` | `7380edb40832cc974606eddd2651b9b765712ac9bdb55cdb1ae1e7a83d450068` |
| `DecimalMachineZFC.lean` | `778af71680ec6aadd9858d30ace87c25012ac6b9dac02e2a483094401fc06107` |
| `Bridge.lean` | `c57457f028f0fca0279a95deb3950665bb663473adeaae32b32c5fa772b24114` |

I read both complete target files before execution and re-read the complete
MarkedWindow, PolynomialWindow, WindowCarry, CurrentCarrierArithmetic,
ThirteenCarrier, ThirteenCarrierSoundness, DecimalMachineZFC and Bridge
sources. The literal Carrier65 polynomial/evaluator and fixed mask/kernel
definitions were checked against these bindings. Their complete sources
and the arithmetic/native proof chain had been read in the preceding
author and peer tasks; this review does not claim a new full-chain replay.

`CurrentPolynomialWindow2011.polynomial` is exactly
`Carrier65.polynomial CurrentWindowCarry2011.ports`. Its four ports are
the fixed tuple

```
[beta, (CurrentKernel2011.K : ℤ), lowPort, highPort + beta].
```

Here `rho=2^47`, `beta=rho^2011−1`, and the exact finite low/high masks
are those already bound to the maintained recipe. The source high mask
is shifted by beta exactly once. `K` is the fixed natural stencil integer,
not a parameter quantified by the new endpoint. The private
`polynomial65_eq` is proved by reflexivity, so the arithmetic-frontier
polynomial and the actual window polynomial have the identical entire
port tuple, not merely similar bounds or an existence correspondence.

The domain remains strictly positive independent integer coordinates:
`v : Fin 14 → ℤ` with `∀j,0<v j`. `PositiveZero` explicitly quantifies
that same domain. No claim is made here about zeros with arbitrary
integer signs or allowing zero coordinates.

`polynomial_zero_blank_halts` obtains one original `MarkedWindow` from
the literal positive polynomial zero. Its positive natural N supplies
both `NeZero N` and `NeZero(N*2011)`; the latter follows from positivity
of the fixed2011 multiplier. Unpacking the dependent window retains its
original source assignment, Boolean word, carries, digits, and chosen
tile assignment. The selected marked-word theorem is already derived
from those same data. No new source equations, phase alignment, count,
occupation, native window, calibration, run or rectangle premise is
introduced at this composition point. The exact natural rank-derived
stride is carried into the marked word; Soundness accepts that stride
without a coprimality or least-period condition.

The actual marked-word soundness theorem then yields blank halting of
the literal decimal-decoded machine. `polynomial_zero_zfc_refutation`
applies the already checked exact machine endpoint to produce
`BProv ZFCax_s [] Form.fBot`. The machine endpoint composes the complete
decimal/dense machine conjugacy with the current `KEndpoint215`, whose
source SHA256 is
`77b71164cf3cac4303ab786852e58969bc5c7332c5261aecfc22a63d3a39dfc9`.
The imported current endpoint object is explicitly pinned in the replay
manifest. No older machine or alternate axiom predicate is substituted.

`ConZFC` is exactly the existing Bridge definition
`¬ BProv ZFCax_s [] Form.fBot`. Consequently the no-zero theorem is the
contradiction between a positive zero's actual blank halt and the existing
`blank_nonhalting_iff_conZFC`. The existence formulation simply unpacks
`PositiveZero`; it does not change the consistency predicate or domain.

For the thirteen-variable forms, the same fixed K and masks are passed
to `polynomial69`, `polynomial70`, and `polynomial71`. Actual K positivity
is derived from `K_pos`, not assumed by the exported theorem. The proof
uses the backward directions of the already established positive-zero
equivalences to restore a positive fourteen-variable zero. In particular
the thirteen-to-fourteen soundness direction has an explicit restoration
map: transport is restored after divisibility, and the signed auxiliary
ordinate is replaced by its nonzero absolute value. There is no new
machine/controller or fresh-private-seed premise on a thirteen-variable
zero.

The focused checks specialize the result directly to
`Carrier65.value CurrentWindowCarry2011.ports v`, not an unspecified
polynomial alias. They cover each of the three thirteen-variable forms.
`thirteen_zero_refutation` uses the direct restoration theorem on a
disjunction of all three actual evaluations, and produces the same
syntactic ZFC refutation. This checks the restoration's positivity and
the definitional equality of its entire output polynomial with the
fourteen-variable endpoint.

Independent fresh replay used Lean `v4.32.0`, `-M6000 -j1`, and a new
temporary object namespace `/tmp/current-soundness2011-controller-peer`.
All entries belonging to the two reviewed stems were excluded from the
prerequisite symlinks. The main was compiled freshly into that namespace,
then the checks imported it through an explicit first-priority
`LEAN_PATH` overlay. No shared source or object was modified.

```sh
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env bash -c \
  'export LEAN_PATH="/tmp/current-soundness2011-controller-peer:$LEAN_PATH"; exec lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentSoundness2011.lean -o /tmp/current-soundness2011-controller-peer/DiophantineConsistency/CurrentSoundness2011.olean'
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env bash -c \
  'export LEAN_PATH="/tmp/current-soundness2011-controller-peer:$LEAN_PATH"; exec lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentSoundness2011Checks.lean -o /tmp/current-soundness2011-controller-peer/DiophantineConsistency/CurrentSoundness2011Checks.olean'
```

Both exited zero. Main:3.52 seconds,3332460KiB peak and no Lean diagnostics.
Checks:4.08 seconds,3329792KiB peak. All six intended axiom reports contain
only `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx`, custom
or native-decision axiom occurs.

| Independent artifact | SHA256 |
| --- | --- |
| Timed main log | `194c1cb734b44fb1db1f53358439f9e82cdc4147dbeeaef81ceba1058ec10511` |
| Timed checks log | `3cdceb633c11774d258e60691acd9ad4400e9c7dfc27accf7c9835d1bccdb817` |
| Fresh main object | `50883df97a6789c2c328e63da188b0ea7719e5aea68764c1c078a765b39e61a6` |
| Fresh checks object | `d4134c1f18f97c0ee35f49999c5ff71fbd6fb6aa8f65c4d7e3210f9c2f0f8a7c` |
| Input source/object/toolchain manifest | `7adecbecb279c904979594d8c2fb535b5282f7af8eae05d6cb7594e12f5904ef` |

The fresh main object is byte-identical to root's frozen original. No
shared checks object existed; that independent object was saved only in
the temporary namespace. All34 recorded inputs were rehashed unchanged
after replay. Existing prerequisite objects were reused; this does not
claim a fresh replay of the whole native or machine endpoint closure.

Scope: the packet proves that every positive zero of the actual maintained
fourteen-variable polynomial, or any accepted thirteen-variable form at
the same fixed ports, gives a syntactic ZFC refutation. Thus ConZFC excludes
such positive zeros. The reverse implication from inconsistency to a
positive zero, the full equivalence, and an internal-ZFC formalization
are explicitly not claimed by this packet.
