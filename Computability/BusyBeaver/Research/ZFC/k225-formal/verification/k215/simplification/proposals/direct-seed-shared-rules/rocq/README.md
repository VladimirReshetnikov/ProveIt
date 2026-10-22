# Rocq: one propositional development for both named calculi

**Checked component refactor, not a rebuilt K215 endpoint.** The source baseline
is ProveIt `6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95`. Both actual named-calculus
instances compile with Coq 8.18.0, all 142 previous theorem signatures compile,
and the unchanged downstream `ZF.L1_LMeta` and `K215F.L224Meta` compile. Recursive
`coqchk` checks the three consumers and their dependencies. The audit prints 26
closed assumption reports: the 12 public propositional rules in each calculus
and the two metatheory results `ae_sound` and `malpha`.

## The reduction

The two old files repeat exactly the same 71 derivations: 59 intermediate
`llp` theorems and 12 public `lpc` theorems. Their formulas and proof bodies
agree after the documented predicate/constructor/name renaming. A shared
`PropositionalRules` module functor now needs only a formula type, implication,
negation, a theorem predicate, modus ponens, and the B1/B2/B3 schemes.

It does not inspect formula syntax and requires no equality or quantifier axiom.
The three old proof bodies that selected `Weq 0 0` as an arbitrary formula now
select their already-bound `w0`. This removes even an inhabited-formula premise.
The classical principles are the object calculus's B2/B3 assumptions, supplied
by constructors in each actual instance; no host classical axiom is added.

`proof/L1_LProp.v` includes the standard instance under the previous names.
`proof/L224Prop.v` gives transparent same-name aliases for the restricted
instance. The definitions of `lprov` and `lprov224` are unchanged. In particular,
the restricted equality-vacuity axiom is not strengthened.

| Production source scope | Before | After | Reduction |
| --- | ---: | ---: | ---: |
| Two old files / shared core and both facades, lines | 297 | 261 | 36 |
| The same scope, UTF-8 bytes | 23,160 | 16,001 | 7,159 |
| Distinct maintained derivation bodies | 142 | 71 | 71 |

Counts include comments and blank lines. They exclude the unchanged source
dependencies and the additional API test. These are source measurements, not
proof-term sizes or measured endpoint speedups. The byte reduction is 30.9%.
The new generic file is 161 lines / 11,747 bytes, the standard facade 14 /
439, and the restricted facade 86 / 3,815. Keeping the standard duplicate and
adopting only the new core plus restricted facade would instead **add** 97 lines
and 3,653 bytes. The reduction requires sharing across both clients.

## Reproduce

With Coq 8.18.0 on `PATH`, run:

```sh
python3 generate.py
python3 check.py
```

The bundled input snapshots make this check self-contained. To restore them
from external checkouts instead, use `prepare_from_checkouts.py` with the three
arguments documented in its header, then run the same commands. It verifies
every input against `evidence/source_manifest.json` before writing it locally.
The check is serial and writes its objects to `build/`; it does not modify a
checkout. The only compatibility edit in a consumer is changing the single
`From Stdlib Require` import prefix in `L224Meta.v` to `From Coq Require`.

`proof/PropositionalAPIAudit.v` restates all 142 original statements, rather
than checking only inferred alias types. The 26 printed results are in
`evidence/K215Common.PropositionalAPIAudit.log`. Source hashes, object hashes,
module timings, exit codes, and the recursive check's exit code are recorded
in `evidence/check.json`. Object files are omitted from the deliverable.

## Production adoption is still a separate step

The packet supplies a checked component and patchable facades; it does not
silently revise the pinned upstream dependency or its hashes. For production:

1. Install the common module in a maintained `K215Common` logical root and add
   its `-Q` mapping to the selected source build. Register it in the dependency
   plan and manifest.
2. Add a reviewed source overlay for `ZF.L1_LProp` at the pinned Jeff reference,
   while retaining the original checkout and its input identity. A new explicit
   overlay must have its own source hash; the old upstream hash must not be
   presented as the hash of the refactored source.
3. Replace `K215F.L224Prop` by the facade. Replace the duplicate-generation
   branch of `rocq224/tools/gen_l224.py` by the facade producer, then update
   `rocq224/src/L224Prop.v` and the 217-to-215 regeneration chain.
   `regenerate217.py` currently includes `L224Prop` in `CALCULUS`, and
   `regenerate215.py` copies that result with a namespace change. Preserve that
   namespace substitution while sharing the common proof core. The historic
   `gen_l224.py` contains absolute workstation paths and is not a portable
   producer as written; the packet's `generate.py` is the reproducible producer
   for these proposed facades.
4. Update the exact source/producer bindings, rebuild the whole K215 closure
   with the required Rocq 9.1.0 and stdlib 9.0.0, rerun its endpoint assumption
   reports, and run recursive `coqchk`. Check relevant legacy clients too.

No maintained generator, reference pin, proof endpoint, or machine table has
been changed by this packet. `patches/` contains source diffs for review, not a
claim that the current frozen production driver accepts them without the
explicit integration above.

## Relation to earlier proposals

This is an implementation of proof sharing at a remaining Rocq duplication
boundary. Lean already shares named-calculus derived rules; the new work is the
Rocq common propositional core, both exact adapters, and downstream/API checks.
It does not rediscover the 58-step rho8 core, certificate symmetry, normalized
source certificates, the candidate scheduler, or positive simulation contracts.
The next analogous step is sharing deduction/metatheory, with equality-vacuity
admissibility explicit; that extension is not part of this checked packet.
