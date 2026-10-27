# Actual DagPerm root: independent review and replay

27 October 2026. **PASS; no mathematical or source correction requested.**
The complemented47 reviewer read the complete frozen 534-line main and
61-line Checks, the author receipt, executed driver and cache planner, and
the actual imported command/fetch/run contracts. Two independent fresh
private builds pass. Both object files and both complete logs are
byte-identical to the author's final results.

| Module | Source SHA256 | Object SHA256 |
| --- | --- | --- |
| ArithmeticDagRootPerm222 | 0aae5535e9c02c3685ae0996db759ebad2485a8f57d609c680d8e3af0ebd03a8 | e26655bd289a1ba913a5d4db93f05b1473827476ef3a47af95905cf039d0eded |
| ArithmeticDagRootPerm222Checks | 783ced636818c7b1723592a764f0695323fdba88444aa4a9c83c466e52c0bddb | 323f805544d379b4651ab8ebd804131f0d2267e48ece17bdbe19db49faf5a28c |

## Mathematical review

The equality proof covers arbitrary internal IΣ1 counters. At node463 the
represented file function subtracts the same bounded internal iteration
count from both counters. The two order branches exit correctly, and the
466 loop clears the remaining first counter. Neither the counters nor the
runtime witnesses are restricted to standard natural numbers. The actual
`ArithmeticDagRun.run_iterate` contract retains Sigma1 definability of G and
fixes an occurrence before internal induction. H supplies intermediate
states and does not require a separate definability premise. Equality has
a normal exit; either strict inequality has the specified break exit, with
scratch fields cleared. This yields the actual MP150, NIP152, and gate457
contracts, including false-cache1 halting and both label-collision cases.

The fixed 156-atom AX word is checked against the actual node chain by a
kernel proof. Its structural Nat induction traverses a fixed finite
certificate, not a variable internal runtime. Each macro already gives an
actual internal run. The symbolic fold retains old-d GEN, rho6(a,c), growG,
dominated rho8, and the helper-free bundle. The AX reader consumes y before
x, while its formal effect uses a=d+x and b=h+y. No axiom-validity, freshness,
nonzero-label, or valid-raw-code premise is inserted.

The selector proof covers 0,1,2,c+3 in the internal model. NIP and DROP
consume no payload; MP consumes one; AX consumes two. `command_step`
constructs the physical boundary with clean scratch registers from arbitrary
working data. It does not assume that the caller's semantic working fields
are valid or clean. Fetch133 treats an exhausted pointer as a new candidate;
raw0 at pointer1 is executed. Actual command/fetch graph equations bind the
result to `enumValue`, rather than to a separately supplied execution.

`root_step` has exactly the boundary file
`[S,pl,t,d,0,0,np,h,0]` and arbitrary internal inputs. Its alternatives are
actual scheduler result0 with a halt run, or that same actual live successor
with a normal root run and `pl' < pl ∨ np'=np+1`. Progress follows from the
existing actual parser/fetch bound. The final theorem assumes no root run,
standard-time bound, or old254 runtime correctness theorem. Focused checks
include both unequal counter orientations, all-zero equality, c=0 AX, the
physical register projections, cache1 halt, and initial candidate4.

## Authentication and independent replay

The selected reachable source/header DAG was independently reconstructed:
149 custom modules, including 95 Foundation, with 434 cached artifacts,
39 explicit package/toolchain boundary names including Init, and 117
boundary companion observations. Zero prerequisites were rebuilt. The
accepted ROOT macro supplement selects the exact object at
`/tmp/arithmetic-dag-macros-perm222-root-y_v4hr6m/lib`; its historical author
provider is retained as provenance rather than substituted for that input.

The peer authenticated the complete five-file plan bundle, all seventeen
author evidence files, both historical author attempts and their immutable
snapshots, every selected source/object and current import header, the
accepted macro supplement, and the final author's input profile. Historical
driver snapshot substitutions preserve exact bytes. The original failed
author attempt remains preserved and is not counted as a peer failure.

The private LEAN_PATH contains only the selected custom overlay and the
recorded package/toolchain roots. All 590 actual first-provider artifacts
were compared: 434 custom artifacts plus 39 boundary primaries and117
companions. Current Foundation trace/output-hash observations additionally
confirm all95 recorded compiler/source-path/output bindings to Lean4.32.
These are rechecks of accepted cached provenance, not a fresh Foundation or
package-source build; package companions remain current observations rather
than retroactive capture claims. In total the peer made 8,342 hash comparisons
over2,083 distinct paths, including final unchanged-input checks.

The executed peer driver was fully read before running. Each invocation used
pinned Lean4.32, `-M6000 -j1 -DElab.async=false`, one thread and a512MiB reserve
before and after compilation. Both outputs are new regular files in
`/tmp/arithmetic-dag-rootperm222-peer-p41b9lmc/lib`; cached objects are private
links. No shared object or source was changed.

| Fresh leaf | Seconds | Peak RSS KiB | Exit | Object and complete log |
| --- | ---: | ---: | ---: | --- |
| ArithmeticDagRootPerm222 | 15.233 | 2150376 | 0 | byte-identical |
| ArithmeticDagRootPerm222Checks | 2.101 | 1844088 | 0 | byte-identical |

The main log is empty. Checks reproduce all13 axiom reports exactly:
`axWord_checked` uses only propext; the other12 use only propext,
Classical.choice and Quot.sound. There are no warnings, errors, sorry axioms,
or failed peer attempts.

The frozen [peer replay packet](arithmetic-dag-rootperm222-peer-replay.json)
has SHA256 `8fac1519929603a2bd9eb52c5bd5ed74b00e8308684c5da66636b153600e1690`.
The [12-file evidence manifest](arithmetic-dag-rootperm222-peer-replay/FILES.json)
has SHA256 `460cf124287e0307cc3638e412908d874b694f2923acc48958a46d95acfab7e0`.
The author packet remains
`47136eefb13b4fedd512e160a3538ba7fb96b5d456ebbe47d37805f41680e65a`,
and the exact approved cache plan remains
`99ab05b4c499f031c65a58fc426777fac55ecc5584cfbd5a790eb2698cbcfa58`.

## Independence and limits

I did not author this RootPerm leaf or its new runtime proof. I previously
reviewed Fetch, DagLoops and Control215Table, and authored some transitive
native/arithmetic215 prerequisites appearing in the provenance. This review
does not independently re-prove my own earlier work or claim a fresh build
of the entire closure.

This packet establishes the actual one-root execution theorem. Full internal
scheduler/control halting correspondence, positive clocks,215 tape/sites/boot,
source-ZFC interpretation and the final HA equation theorem remain separate.
Only new peer evidence and private outputs were written; no frozen source,
shared documentation, display or Git state was edited.
