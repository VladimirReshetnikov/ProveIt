# Internal C222 relational core and indiscernibility — independent review

26 October 2026. **PASS; no source correction requested.** Reviewer:
`circuit_reduction`, author of neither packet. This is an independent complete
source/math review and reauthentication of the existing author/root replay
records. As requested, I did not launch an additional compiler replay or alter
any reviewed source, dependency object, or shared document.

## Exact scope and pins

I read all 180+48 lines of RelationalCore and all 260+49 lines of Eind,
both author receipts and replay metadata, and the root replay records. I also
read the actual CProv definition/node constructors, EqualityCore deductions,
and the actual C222 row override used by these proofs.

| Source under `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/` | SHA256 |
|---|---|
| `ValidatorRelationalCore222.lean` | `3246a40dae816446a560652ff334ad44026752e176e577328622b236855a47a9` |
| `ValidatorRelationalCore222Checks.lean` | `df968c57dc38ef08269b097fdf6374c0e1fb94b23e8609aaf3885605396e9747` |
| `ValidatorEind222.lean` | `09ee7d8f43c4bf35486043beb4cfa191ad29ca5891797f0b2919476c825025f3` |
| `ValidatorEind222Checks.lean` | `867662cc3efaef099f4e09b06ac78beeeb4f725c6dfd6b7aef0cc57ffed0e16b` |

Author replay manifests:
[RelationalCore](validator-relational-core222-replay.json),
`119ef3f9db0800d558e0a9e05d7e76a0363e7263dd488c1d33f5eaf391d2afcf`;
[Eind](validator-eind222-replay.json),
`4874421e3a406aee5f59a52692790f8c1afaa24b0dbb6b6c4629fe225fbe12a9`.
Root records:
[RelationalCore](validator-relational-core222-root-replay/ROOT.json),
`7ae3e8a2373c60f5cbc0174699f85dc1fddd830d32bcc5bda701011b6b4116ea`;
[Eind](validator-eind222-root-replay/ROOT.json),
`b596553ac2f56bdf31a0df1edc2c3a23b161dca7f8c024cbe5617238b703022f`.

## Mathematical findings

All code values and labels range over an arbitrary internal IΣ₁ structure.
`CProv p` is the actual assertion `∃ code, ArithmeticHistory222.value code =
p + 1`. MP, GEN and the finite logical certificates are realized by the
actual checker nodes. In particular, node 9 is `growG`, and node 11 is the
helper-free seed with exactly `c ≠ a` and `c ≠ b`. The unchanged nodes use
the retained row kernel. There is no assumption of semantic seed validity.

The relational layer's open deductions use explicit finite lists. Each
`ded1`/`ded2`/`ded3` discharges that list before its result is passed to GEN.
`all_under_two` requires vacuity of both open resources, and
`all_relational` explicitly requires `Vac x h`, `Vac x q`, `Vac y h` and
`Vac y (wal x p)`. Thus the two-binder argument does not generalize an
unrestricted open assumption. Existential elimination uses the exact
matching binder and a supplied/derived vacuity certificate. The encoded
classical propositional reasoning comes from the actual C222 checker;
these are not additional classical inference rules in HA.

The indiscernibility definition uses both membership directions at the
fixed binder `a + b + 1`. Fixed relational alpha conversion and
specialization are derived from the relational layer, rather than assumed
as arbitrary substitution or proof-renaming principles. `Eq_Eind` uses
primitive equality's available vacuity only at the actual helper
`wel a b`; the Cantor bounds prove that helper differs from both labels.
It then changes the membership binder to the fixed auxiliary. There is
no arbitrary-binder primitive equality-vacuity oracle.

The two membership transports, existential indiscernibility witness and
Euclidean law preserve their exact coded conclusions. `Eind_vac` handles
`c = a + b + 1` by first renaming to `a + b + c + 1`, proving vacuity there,
and transporting back under GEN. The hypotheses permit `c = 0` and
`a = b`; the focused checks retain both cases and the auxiliary collision.
Expanded checks end in actual history-value witnesses. No deduction in
either new module calls the external standard-Nat derivability bridge.
That bridge is transitively available in the prerequisite environment;
this review does not claim its module is absent from the import closure.

## Replay provenance and limits

A read-only hash audit matched both compiler/manifest records, all 249
input-source observations, 819 input-object observations, 76 external
boundary observations, author drivers/parent receipts, all final leaves
and saved snapshots/logs/timings, and all 1,146 root prerequisite pins.
These are observations across two overlapping manifests, not counts of
distinct freshly compiled modules. Every root bundle file and each final
author/root object hash also matched. No mismatch was found.

The recorded fresh scope is four author leaves and four independent root
leaves using `-M6000 -j1 -DElab.async=false`. The root main logs are empty;
the 24 reported axioms contain only `propext`, `Classical.choice` and
`Quot.sound`. All four root objects equal the author's byte for byte.
RelationalCore reuses 124 modules; Eind reuses 125. Each includes 95
Foundation modules and 38 explicit cached external boundaries. This is
not a fresh whole-Foundation/dependency build. The one rejected Eind
check run used ambiguous `one_ne_zero`; its snapshot and failure log are
retained. Only the corrected `_root_.one_ne_zero` run is accepted.

The result is a checked internal finite equality-interpretation packet.
It does not establish arbitrary represented formula/proof translation,
semantic validity of the seed, execution of a counter machine, or the
final HA consistency/equation equivalence.
