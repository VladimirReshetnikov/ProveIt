# Structured register-program components

The remote L2 development through `2628aa9813` supplies `RMDag`, `Dag254`,
`L2Lib254`, `L2Macros254` and `L2Control254`. Independent source review found
the actual statements consistent with the attributed pinned upstream
`RM.v` and `Dag254.v`; all219 program rows were independently compared.
The five modules now compile serially with pinned Lean4.32 in the standard
ZFC runner. Their source checks and a joint umbrella check are recorded in
`results/infinity-l2-integration-verification.json`.

`RMDag` specifies structured termination outcomes, loop restarts and
register transfer/copy/clear routines. `L2Lib254` relates a nine-field record
to that register file. The pairing routine adds P(input1,input2) to its
existing output accumulator and clears its inputs. The two unpair walks
compute `ofNat(P(initial_s1,initial_s2)+counter)`; plain unpairing of the
counter requires the explicit zero-scratch premise.

The macro file proves stack operations, additive reads and all four formula
constructor tags with the actual cleanliness assumptions. The control file
proves the destructive equality test, candidate fetching, MP and both NIP
branches. Equality testing clears both compared registers; NIP clears the
old parameter before popping and halts exactly when the tested parameter
is1. These details match `Enum254`, rather than a simplified register model.

The `L2Lib254` introductory phrase saying every loop is transfer/copy/clear
is too broad: the pair and unpair loops have their own proved shapes. The
actual theorems retain these distinctions. The later two files provide the
macro/control results previewed by that introduction.

This checkpoint does not prove the AX branch or the root enumeration loop.
The DAG unfolding and the literal `Prog254` tree are also different trees:
both have6459 cells, but their depths are96 and34. A literal tree identity is
therefore unavailable. The published3010-entry path bisimulation, or an
equivalent justified relation, remains necessary before connecting this
structured program to the existing path semantics. Concrete binary dispatch
is another separate simulation; the new `BreakSite253` theorem proves only
its stated001→1 site. Source review and the local kernel checks supply no
whole-program or machine endpoint.

The later `798aaa6ce1` adds `L2Axioms254`, generated from the same pinned
DAG. Its110 generated node lemmas compose the actual AX subtree into the
state transformer `f1`, with `l1` proving `Rn (.node 1) st (f1 st)` and `c1`
preserving clean scratch registers. The special node35 transformer includes
its entire remaining tail through46/58; it is not just a read operation.
The generated860-line source reproduces exactly in a scratch copy and passes
pinned Lean4.32 in1.587seconds, with standard-axiom audits for `l1` and the
gate theorem, and an axiom-free `c1`. Evidence is in
`results/decoder-duplicate-integration-verification.json`.

Independent symbolic review of the181 macro calls matches the intended
eight logical rows, saved old formula, generalization using the old parameter,
additive second parameter, two consumed literals and final gate. However,
the source header's assertion of a final symbolic equality with
`Enum254.axStack`/`gate` is premature at this commit: no such equality is
among its declarations. The actual proved result is execution to `f1 st`.
Identifying that transformer with the abstract AX command and completing
the root loop remain separate obligations; the earlier paragraph describes
the previous five-module checkpoint. Read-only reproduction and comparison
records are retained in `/tmp/zfc-l2-axioms-read-review-zluls6ey/`.


## Full root correspondence after the earlier checkpoints

The subsequent merged `L2AxiomsEval254` and `L2Root254` close the AX and root
obligations stated above at their historical pins. All 110 closed forms are
checked against the actual generated transformers; both generators reproduce
exactly on scratch copies. `ax_eval` now identifies the actual AX stack and
gated bundle. `root_step` covers MP, DROP, NIP (including halt) and AX, with
candidate fetching and both parameter reads. Determinism gives `iter_iff`;
the two initial nonhalting candidates connect the enumerator's zero state to
nextproof = 2. `program_halts_iff` therefore proves actual structured-program
halting from those registers iff numerical falsity is derivable.

Independent read-through and serial pinned Lean 4.32 checks pass for the
current AX composition, closed forms and full root source. Nine principal
axiom audits and three actual callers are included with the new `ProgramZF0`
composition in `results/l2-program88-integration-verification.json`. All use
only standard Lean axioms. Source-identical prior dependencies are reused;
no full closure or binary bootstrap rebuild is claimed.

The remaining different-tree issue is unchanged: this theorem concerns
`IterHalts Dag254.dag254`, not the 6,459-node literal `Prog254` path program
or a binary transition table. Its endpoint cannot be spliced into the
existing RM331 tape theorem by treating the two tree shapes as identical.
The new `ProgramZF0` consequence is likewise at the structured-program layer.
