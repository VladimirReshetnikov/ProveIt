# Independent actual C222 compiler-row review

26 October 2026. PASS, no requested changes. Root authored the new
214-line main and 37-line checks. Controller-certificate independently
read both complete frozen sources, the complete private driver, author
receipt and metadata before replay. The actual Row222/Row254 definitions,
Leaf/Rule contracts, fixed circuit graphs and unrestricted rho8 theorem
were read against every branch. The reviewer authored earlier Row222,
History222, SequenceHistory, Block/Leaf/Rule dependencies and contributed
the current cache/architecture proposal; this receipt independently
reviews root's new row implementation, not those prior authorships.

The graph's fixed slots are `(out,tag,payload,minorWord,majorWord)`. Its
children are words, distinct from checker values in `row_contract`.
Unbounded existential intermediate fields are appropriate for rejected
outputs; no intermediate is incorrectly bounded by zero. The twelve
disjoint branches and explicit invalid-tag branch cover all internal data.
The unconditional truth branch emits discard even at rejected payloads;
correctness derives payload0 from actual acceptance.

MP extracts the real two successor child values and the actual major
implication from MPGate, then invokes the accepted minor-first contract.
GEN uses its supplied selected child and retains label0/conclusion1.
Tags3–7 match the actual rho1–rho5 leaves. Tag8 uses the exact physical
rho6 adapter `leafWord 6 a 0 t 0`, tag9 uses actual growG, and tag10 uses
the uniformly chosen unrestricted rho8 circuit without a false dominance
assumption. Tag11's c≠a,b gates are proved from actual row acceptance;
c0 and a=b are not excluded independently. The last branch contradicts
acceptance of an invalid tag. All-top/all-stack quantification survives
each use of the child contracts, including the major MP saved stack.

The chosen circuit is fixed before any model/input. Its choice theorem
was instantiated at Type0, and `rho8_contract`/`row_contract` explicitly
remain at Type0. The numeric graph interpretation is universe-polymorphic,
which does not promote the selected contract to higher universes. The
noncomputable graph declarations accurately reflect the external finite
choice; there is no claim of executable extraction of the circuit or
arithmetic proof serialization. No internal circuit interpreter, desired
global compiler correctness, source-seed truth or standard-code premise
is assumed. No mathematical finding arose.

Main SHA `578bedf1ab0932e549ecfcb248350fbac28075684a2616b0ff36443f44ee261c`;
checks SHA `436b32e4704803d5a7107b000b70ab2ca2b67950e7c8401494125864bc644def`.
The author packet `841882f09456821f479335d647e6a6dad643d00081efa4095aa69c81198f88e1`
and all 14 preserved author files were reauthenticated, including its
first noncomputable-annotation failure. That failed author attempt is
retained without treating its secondary diagnostics as successful audits.

Independent fresh main/check replay passed in 13.474s/1.864s with empty
main output and six reports containing only `propext`, `Classical.choice`
and `Quot.sound`. Peak RSS was 1,848,592/1,817,840 KiB. Both objects are
byte-identical to the author's:
`dea3c12d8060939ac0bb0996e57cc31d96c350c98bb182812de826e930d80a84`
and `4e192676e97f7d7839181667fcb5b2fd883aae86eb93366fd96268ff3b957cd1`.

The private overlay is `/tmp/proof-word-rowperm222-controller-peer-80tadtoz/lib`.
It reuses exactly 132 cached modules, including 95 Foundation modules,
417 artifacts and 38 explicit external boundaries. Current source hashes
and import headers were checked. All 1,888 inherited observations plus
explicit peer/manifest/source/artifact checks total 2,480 repeated pins,
verified before and after compilation. Only the new two leaves were
compiled, with target stems absent from the cache and fresh regular
nonsymlink outputs. Lean4.32 used `-M6000 -j1 -DElab.async=false`, explicit
package providers, no shared project cache or `LEAN_SRC_PATH`, and a 512MiB
reserve checked before each invocation. No dependency/Foundation build,
source edit, shared-object change or Git mutation occurred. There were
no failed independent compiler attempts.

[Peer replay](arithmetic-proof-word-rowperm222-peer-replay.json) SHA
`8defac652bd5c31eb2f07eab14310e18b4371d608c82647d1a9c153a6c2c6dd3`;
[nine-file evidence manifest](arithmetic-proof-word-rowperm222-peer-replay/FILES.json)
SHA `ad5c1c5d904d574fe8a0dd4dcb071e5b3611dc70c13e37101a2daea316c9f524`.
Complete input pins, driver, commands, snapshots, logs, timings and result
are retained; objects are pinned at their private paths. Proof-history
recursion, Π1 prefix correctness and the final HA equivalence remain
subsequent checkpoints, not conclusions of this row review.
