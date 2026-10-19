The exact source snapshots, reviewer scripts, original note and records named
below are preserved in [history.json.gz](history.json.gz). This is a review of
the specified historical commit; later implementation does not change its scope.

---

# Packed W3 source review — 9f2276a8c3

**The concrete equivalence is now present in the Lean source.** Unlike the
previous ten-entry probe, `ControlBisimRotation240.lean:50–69` supplies four
kernel checks covering `[0,1000)`, `[1000,2000)`, `[2000,3000)` and `[3000,3862)`,
assembles `check_all`, and establishes the zero-offset initial entry. Lines
86–99 apply the generic theorem to prove equivalence from control 1 and every
internal file in every IΣ1 model. No mathematical blocker was found in this
source review. This is an equivalence of **the two interpreters defined by the
packed literals**; it is not yet the exact binary240 PA endpoint.

Reviewed commit: `9f2276a8c3f4c90e6f847864c2151715aa3baadf`; accompanying plan:
`d073d35d5356ffea0878846581716ac337e796a3`. Exact snapshots/Git blob identities
are in `inputs.json`, with the original tree-based interpreter retained under
`deleted-source/`. No supplied Python, generator, proof checker or compiler was
run, and no repository file was changed. `static-review.json` records 66,087
reviewer-owned source/literal checks, not a fresh Lean PASS.

## Encoding and the theorem's actual premises

`PackedTables` uses least-significant-first fixed slots: each row has 33 used
bits in a 36-bit slot, and each entry has 86 used bits in a 96-bit slot. The
three/ten high padding bits are zero in every current slot. Decoder field
positions agree with the emitter. All raw register fields are below nine, so
the decoder's final `% 9` does not alias a malformed current field; generic
decoding remains total for arbitrary numbers. Controls and certificate
references fit their declared 13/12-bit fields, and no data extends beyond the
declared slot counts.

Own static decoding compared **all 3,862 entries** exactly with the previous
literal certificate, including the initial `(1,1)` pair and ten nonzero B-side
unit offsets at physical coordinates 6/7. It also compared **all 12,915 rows**
(6,460 DAG and 6,455 Rotation240) with an independently authored finite
source-path reconstruction from the exact DAG and candidate sites bytes.
That comparison confirms the physical permutation and outgoing control
indices as data; it does not replace the missing Lean tree/table theorem.
No machine run or semantic certificate-check algorithm was invoked.

`table` is `List.ofFn` of decoded slots. `rowsOf_some` proves that a successful
packed lookup is the corresponding list element and has nonzero control;
`spec_get` therefore connects the packed row to the represented step without
assuming a generator is correct. The new `nextRows` deliberately ignores
`next1` for non-test opcodes, matching generic row semantics and removing the
old equal-successors premise. The represented tables remain Σ0, the step Σ1
over IOpen, and the run Σ1 over IΣ1.

The concrete `halts_iff` has no residual certificate/check/closure hypothesis:
`check_all` discharges every entry, `cert_zero` discharges the start pair, and
the existing file/projection/write laws, nonzero live encoding, represented
run laws and both `spec` lemmas discharge the generic theorem's hypotheses.
Its existential times and file `x` are internal model elements. The use of
positive segments and absorbing halt is inherited from the unchanged generic
bisimulation, rather than a claim that both runs use the same clock.

## Remaining connections

The concrete wrapper imports only `DagControl254`; it no longer imports
`TreeRotation240`, `Dag254` or `RMEquiv`. Its two programs are defined by
`BisimCertRotation240.tableD/tableR`, not by a tree computation. This is a sound
way to make the equivalence cheap to check, but names alone do not identify
those programs with the intended operational semantics.

For W6, prove the packed Rotation240 list/lookup agrees with the catalogue
derived from `TreeRotation240.tree`, including the physical register map,
control numbering, start point and successor paths. Then connect its internal
run to the fixed binary240 arithmetic run and seed/bootstrap encoding. The
new external Binary240 PASS reported by root closes a separate external
endpoint; it does not furnish this arbitrary-model operational bridge.

For W4/W5, implement the promised internal structured DAG semantics and prove
the root-occurrence/exit-map binding to the packed DAG rows, then port the L2
constructor contracts and scheduler/validator connection. `ArithmeticDagRun`
and `DagRun254` are referenced prospectively in documentation but neither file
exists at `d073d35d53`. A finite root-row check by itself cannot prove their
generic composition lemmas, internal Σ1 iteration or logical-register encoding.
The plan explicitly treats these as next work; the old Prog254 control
contracts are not automatically applicable to these new numbered rows.

The plan's “W3 closed” wording is accurate for the **packed-table interpreter
equivalence**, with these external bindings still open. The final PA sentence
about the exact machine, and its proof/audit, are not supplied by this commit.

## Evidence and resource scope

Upstream reports zero warnings, axioms `propext`, `Classical.choice`,
`Quot.sound`, roughly 90 seconds for four chunks, and profiling improvements
from over 500 seconds per 100 entries to 1.6 seconds and from about 4.7 GB to
1 GB. These are attributed commit-message/plan reports: the reviewed commit
contains no audit file, raw command/log, object pin, verification JSON or
profiling record establishing those measurements. This review does not upgrade
them into locally reproduced results or claim a default-limit proof run.

The concrete wrapper explicitly retains `maxRecDepth 100000` and
`maxHeartbeats 0`; ArithmeticControlTable, File and the generic Bisim retain
8,192/4,000,000. The old per-part data settings 200,000/unlimited disappear
with the packed representation, but the complete wrapper still has unlimited
heartbeats. Checks use `decide +kernel`. The changed source contains no new
axiom/hole or supplied native computation shortcut on this inspection.

One minor documentation defect remains: `PackedTables.lean:18` mentions
`certOf_some`, which is not declared. `certOf` is used directly and the proof
does not depend on that nonexistent name; removing it from the overview is
sufficient. “36-bit/96-bit slots” is correct; the payload widths are 33/86.

Reviewer: drop_contract, author/reviewer of the preceding W1/W2 integration
reviews and external proof work, not author of this upstream change. The
review is read-only and does not take over the upstream PA implementation lane.
