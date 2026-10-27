# Actual DagPerm macros: author checkpoint

27 October 2026. The controller agent authored and fully read the final
817-line `ArithmeticDagMacrosPerm222` and 68-line Checks, the executed private
driver, and the relevant accepted execution/loop definitions. Final two-leaf
build PASS. Independent review and replay remain separate.

The sole main import is `BusyBeaver.ZFC.ArithmeticDagControlPerm222`. The new
`IR` and `Rn` use that accepted literal program, table and represented run,
with physical file `[ws,pl,tw,p1,ac,s2,np,p2,s1]`. The field/update identities
are proved. No caller supplies a program, table, occurrence or execution
correctness premise. These are concrete structured-run contracts; composition
to the whole enumerator root is not asserted by this packet.

The exported contracts include:

- `pair162`: add `cantor s1 tw` to arbitrary existing `s2`, clearing both inputs.
- `loop115` and `loop116`: consume respectively `pl` and `ws`, with final
  scratch pair equal to the projections of `cantor old_s1 old_s2 + input`.
  Initial scratch values are unrestricted.
- `read_ac`, `read_p1`, `read_p2`: consume the first proof-list field and add
  it to the original destination, with the scratch pair clean.
- All thirteen actual AX atoms: parameter pushes 166/121/168, push171,
  cons119, wel181, wal180, weq182, wn218, wa178, wex183, readp2_176 and
  readp1_175. Each is a literal formula-code computation, not a CProv theorem.
- The auxiliary value-one push177 and stack pop170, and both fetch133 cases.
  Positive `pl=v+1` becomes `v`; exhausted `pl=0,s1=0` loads old `np` and
  increments `np`, preserving all unrelated work data.

Pairing and unpairing adapt inspected arithmetic proof text from
`ArithmeticL2Lib254`; the formula macros adapt `ArithmeticL2Macros254`.
The old modules' fixed-interpreter semantic theorems are neither imported
nor invoked. Existing generic `ArithmeticDagLoops.transfer/copy2` is
instantiated at the actual nodes. The internal pairing, Cantor walk,
multiply-by-four and rotated fetch loops use explicit Sigma1-definable file
invariants and the accepted internal Sigma1 iteration theorem. Counters and
times range over every IΣ1 model, including nonstandard values. There is no
external-Nat induction on these counters or induction on an arbitrary Lean
predicate. Formula macros have explicit scratch cleanliness; pairing,
unpairing and the rotated loop do not acquire that assumption.

The first compile found a real control-binding difference from the historical
fetch proof: actual node136 is `(inc0,node300)` with node300
`(decnz6,cont2)`, not the old transfer-then-increment tree. That failed source
and complete diagnostics are preserved. The repair proves actual `loop136`
with internal invariant `np+t,s1−t`, including its final increment when
scratch is zero. The second compile needed only an explicit record-field
simplification at that final zero test; two now-unused simp arguments were
also removed. The third main and first executed Checks both pass cleanly.
Fetch theorem statements were unchanged. Inspection of `L2Control222` was
used to confirm the rotated tree, not to invoke its Nat proof. The thirteen
atom list was cross-checked against `L2AxiomsPerm`'s literal `AXAtom` mapping.

Checks state all nine physical slots, zero pairing, zero-input unpairing with
dirty scratch values, an additive read into a dirty parameter, total empty
stack projections, and both fetch branches including raw candidate zero.
There are 22 final axiom reports, all using only `propext`, `Classical.choice`
and `Quot.sound`; main diagnostics are empty, and neither final log contains
warnings or errors. This is not a claim of an already constructed HA proof.

Exact selected closure: 139 cached project modules, including 95 Foundation
modules, 424 recorded artifacts, and 39 explicit package/toolchain boundaries
with 117 companion observations. Zero prerequisites were refreshed. Current
source headers, exact reachable import closure, sources, artifacts and first
providers were authenticated. The accepted root DagControl and PackedTables
providers and their root acceptance state are explicit supplements to the
unchanged historical plan. External `LEAN_PATH` entries are only the pinned
package/toolchain providers; no project-wide shared cache is searched.

Each invocation used pinned Lean 4.32 with `-M6000 -j1 -DElab.async=false`,
one thread, fresh regular nonsymlink output, source snapshots and a 512MiB
disk-reserve check. Final times were 24.245s and 2.246s. The successful driver
performed 1,487 cumulative pin observations; the final evidence freeze
reauthenticated 3,297 observations across all three attempts and first
providers. Historical driver versions are checked against their preserved
executed snapshots, not falsely matched to the later driver. All failed
attempts, commands, inputs, source snapshots, logs and timings are retained.
No accepted source or shared object was edited, and no Git mutation occurred.

| Leaf | Source SHA256 | Object SHA256 |
| --- | --- | --- |
| Main | `3faa5f35de03d12407e2303432197144f2b279c842f785fd8d6ba6a89fa23d7d` | `c225836ef38be24365c6ed0205ad5e5de280b6407c3155ce897553a5c3d17f4a` |
| Checks | `e26bd15e27c2fe2e24f6f631d1c78e61847480516dc30c871422fe0f768c01cd` | `6b3b99af45fb53c914c39e94ea08cfa87742a7ad2573fcb8c983fbf92e48a965` |

Final provider: `/tmp/dag-macros-perm222-controller-author-8ya4kyf6/lib`.
[Replay packet](arithmetic-dag-macros-perm222-replay.json) SHA
`0cf62d5a3d713c31e422929ee60f3e8a4c7fec8e633185ddea059af5f58315ea`.
[Complete 24-file evidence manifest](arithmetic-dag-macros-perm222-author-replay/FILES.json)
SHA `99d4a2cfe83b16eb49315950272833ab32e3bbaf3eb6c5810cc4f3190a56845f`.

The actual equality123/gate, complete AX word/dispatch, root-step composition,
positive-clock and enumerator correspondence, literal215 tape/site/boot
simulation, source-ZFC calibration and final arithmetic/HA equivalence remain
separate obligations. No such endpoint is assumed or concluded here.
