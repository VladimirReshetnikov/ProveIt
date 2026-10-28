# Actual C222 GEN/MP command rules: author record

26 October 2026. The controller agent authored and fully read the final
124-line main, 50-line checks, private driver and relevant accepted command
dependencies. Both final fresh leaves pass. Root's independent replay and
acceptance are separate.

The four exact numeric definitions are genTail/genBlockWord and
mpTail/mpBlockWord, using current shifted-word constructors and represented
append. GEN is DROP;J(i);NIP;AX(i,0,0);NIP^9;DROP;NIP;NIP. The actual loader
J(0) is empty. After loading H from cache0, AX consumes H immediately, so
H=1 is legal. The actual eight-row prefix has rho6(i,i), growG(i,H,i),
rho8(i,H,i,i); its old counter is i, and the chosen ninth row is wal(i,H).
The checked finite selection restores exactly the saved stack S and zeros
both counter and cache. No formula-validity, positive-label or H≠1 premise
is supplied.

MP runs the minor, DROP, then the major at top0 and saved stack P(A,S).
Its exact suffix halts when A=1 or B=1, and otherwise returns (B,S,0,0).
On successful MP the old counter becomes B; the cleanup AX stack is exactly
axStackValue(B,0,0,B,B,B,P(0,S)). Ten NIPs load the saved B without testing
it, then the final DROP/NIP sequence tests B and restores the two explicit
zeros in the non-false branch. Both literal halt branches remain permitted
by Contract. The public gen_contract/mp_contract preserve the original
all-internal, all-initial-top/all-saved-stack Contract without non-false
premises on children or conclusion.

Focused checks cover GEN at i=0 and H=1 together and separately, both MP
false branches, B=0 success, A=B=0 success, arbitrary child contract maps,
the exact major top0/P(A,S), and old-counter-B cleanup. Seven printed audits
contain only propext, Classical.choice and Quot.sound.

Frozen hashes:

- Main source `e381cbdfe636090c9a6e2a0c9082b10e6f33bea22f8de2ca3a7a988283de4fe1`.
- Checks source `98882743bbe2e4dfb08b4926e3bc0fa24ae37acc3bbc3d8bbee6defa045308a0`.
- Main object `c03416125efb63930175222e45710fd61090ce260fa54cf11def06abbc469687`.
- Checks object `c19fa2beb6fa474dd5792b9c50a7698cb2a2f19448f0c7a39c7bb0da9c340121`.

Private objects are regular files in
`/tmp/command-ruleperm222-controller-s2yxzxu5/lib`.
Final main/checks passed in 2.800s/2.334s, with empty main diagnostics and
seven standard-only checks reports. Peak RSS was 1,821,488/1,814,068 KiB.
The initial main also passed, with three unused-simp warnings. Those hints
were removed and the clean main replayed; no statement or word changed.
Checks passed on the first invocation. All three attempts and original
source snapshots are preserved; there was no failed Lean invocation.

The unchanged approved [proposal](../research/c222-command-rule-next-proposal-20261026.md)
and [cache plan](../research/c222-command-rule-next-cache-plan-20261026.json)
are pinned before execution. The sole direct import is accepted Leaf.
Its provisional author primary was replaced privately by root's byte-identical
accepted primary at `/tmp/arithmetic-command-leafperm222-root-peer-4yp69o_l/lib`.
The root acceptance record SHA is
`a50950f0b704ea6bf9d08991b6feb0bee63b5d014526d055d799c7383922c9cd`;
the input metadata retains both original and accepted provider pins.
All124 cached custom modules (95 Foundation),409 artifacts and38 external
boundaries reauthenticate:571 source/artifact/boundary observations, plus
compiler and provider pins, before and after every invocation. Current
imports close over exactly that declared scope. No dependency was rebuilt.

The historical254 RuleExecution and actual Nat EnumPerm definitions were
read as proof-layout guides. No historical semantic execution theorem or
Circuit is imported. The current words differ at the permuted constructors,
GEN loader, rho6 slot, growG row and old counters. Their correctness is
proved directly against the accepted current evaluator. The optional Nat
list-encoding adapter was left out to keep the checkpoint finite and narrow;
no represented circuit/history, unrestricted rho8, global compiler, runtime
calibration or HA endpoint is claimed.

Pinned Lean4.32 commands use `-M6000 -j1 -DElab.async=false`, fresh nonsymlink
attempt outputs and a512MiB disk guard before each run. The cache consists
of private symlinks; external LEAN_PATH entries are package/standard libraries,
not the shared project object cache. No accepted source/object, shared doc
or Git state was edited. [Replay](arithmetic-command-ruleperm222-replay.json)
SHA `8e08f9e7b4934efa3a9a7e475caa8f722ee0d5a93bd8d86294478682e0379857`
and [14-file manifest](arithmetic-command-ruleperm222-replay/FILES.json)
SHA `5c954ef36cbe9f0a1fe0af1053f9e5292ef96f7ab50a757052ff4b429d26b8c3`
preserve exact sources, commands, input/driver pins, logs, timings and objects.
