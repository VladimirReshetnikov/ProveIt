# Actual C222 theorem predicate: author validation

Author: `controller_certificate`. This is an author receipt, not an independent
review. I also authored the actual C222 constructor, history, Nat-binding,
row and template prerequisites; their separate root and peer reviews remain
the relevant independent evidence. No accepted source, shared object or Git
state was modified for this checkpoint.

The frozen main has 125 lines and focused checks have 48. Both complete
sources and execution drivers were read before running, and both sources
were reread after the first successful pair.

| File | SHA256 |
|---|---|
| `ValidatorProvability222.lean` | `a3b50d8088d288ee951f2a9612e624e54ea78814151aaa3a2acc083242ac78b2` |
| `ValidatorProvability222Checks.lean` | `c9422b37c6c3847a0e3516c2fb709301c924ca36a8f228bcc58c5614e5f90a68` |
| `validator-provability222-replay.json` | `30d8f8e282925072f4fd51543ce4727e95e54fa9a96c580b809dbd23446bfa63` |

`cProvDef` is fixed Σ₁ syntax declared before any ambient model variables.
Its represented predicate is exactly
`∃ code, ArithmeticHistory222.value code = conclusion + 1` in an arbitrary
`ORingStructure` model of IΣ₁. All rule closures supply actual new-checker
numeric witnesses. MP takes its major premise first while constructing the
literal node with conclusion, minor code and major code; GEN retains the
whole child. The changed equality rule is explicitly `growG`, with no
assumed `rho7`. The helper-free seed retains exactly `c≠a,b`, so `a=b` and
`c=0` are legal when those gates hold.

The finite propositional interface follows the earlier interface's proof
pattern but imports no `ValidatorProvability254` or old soundness theorem.
It instantiates the existing polymorphic `Lukasiewicz.Implicational`
certificate with actual new MP and row8 witnesses. K, S, Peirce and
composition follow from that generic finite certificate; ex falso follows
by the explicit finite rho6 deduction at false code1. Thus the resulting
`Kalmar.Classical` interface describes C222's actual proof calculus. It does
not add a classical rule to HA.

`cProv_nat_iff` uses the frozen all-code `ArithmeticHistory222Nat`
adapter to prove equivalence with the actual `KCode222.C222`, without an
unproved checker-agreement premise. That adapter's transitive old
History254 import supplies only generic Nat arithmetic normalization; no
old evaluator semantics is used in the new theorem predicate or closures.
The focused checks expose the fixed graph interpretation, major-first MP,
GEN, the full growG formula, both legal seed edge cases, literal false1,
the finite logical interface and actual Nat binding.

The only direct imports are `ArithmeticProofConstructors222` and
`ArithmeticHistory222Nat`. The private overlay
`/tmp/provability222-controller-v9au4606` authenticates 122 custom source
files (95 Foundation), 407 recorded object companions, and 38 explicit
external package/toolchain roots. Every recorded source/object hash plus
compiler and manifest was checked before and after execution. The input
inventory SHA256 is
`2fd0d8df9f097cb269a685d63dc148e48e30445985f2bb0230987886870e11d5`;
the captured repository snapshot is
`88cf5fc90ea7abc2e81be1a01247d2964078965b`.
The inherited cache and external-package scopes are detailed in the pinned
parent receipts; this was not a fresh Foundation or full dependency build.

Both new leaves passed their first fresh run using the exact 4.32.0 compiler
with `-M6000 -j1 -DElab.async=false`, writing only private output objects.
Main and checks took 3.27 and 2.06 seconds; maximum RSS was 1,824,088 KiB.
The main log is empty. All ten intended axiom reports contain only
`propext`, `Classical.choice` and `Quot.sound`. No development failure or
source correction occurred. The final disk check left 1,174,642,688 bytes,
above the 512 MiB reserve.

| Private object | SHA256 |
|---|---|
| main | `5ae10459c6cd6a5e07097113fb4dab4bfcc7a76ec2b4d1e498e601a499238760` |
| checks | `c45a1653217532d5aca3916bd11d93d485f4ac2240e17ed373f9885421a4aef2` |

The replay JSON preserves the complete prerequisite inventory, pinned
parent receipts, source snapshots, commands, logs, timings and output
hashes. Equality-helper/rho7 and seed-projection derivations remain separate
follow-up work. Seed validity, an internal calculus translation, machine
runtime and the HA equivalence are not established by this packet.
