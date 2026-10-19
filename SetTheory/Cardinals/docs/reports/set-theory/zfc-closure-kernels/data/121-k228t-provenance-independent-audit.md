# Independent final audit of K228

## Result and exact artifacts

The final deterministic builder is `build_k228.py`, using Python standard-library
modules only. It reads the exact released K230 table and source, verifies their
SHA-256 pins, and constructs the rotated 230-state intermediate, the 229-state
loop-fold intermediate, and the final 228-state table. It also supplies an exact
state bijection to contiguous working labels `0..227`, with start `0`, dispatcher
`83`, and the separate halt outcome `228`.

The canonical table has 456 transitions and SHA-256
`06726bd731f3a42e3ccd1c4189d80af74ba2d486e333045097480fcaa3313001`.
The original-label final table has SHA-256
`2b791ed22523b9610d43d7440631b27063089d2d1a24cf3bfbe5ace6cf416ea2`.
Its eight changed surviving rows are `63/0`, `63/1`, `70/1`, `71/0`, `80/1`,
`121/0`, `121/1`, and `126/0`; states `79` and `140` are deleted. The receipt
records all before-and-after rows and all four deleted transitions.

The final builder has SHA-256
`05663233f797029aa28361298c57d1c6fafaa007341cd617a07fbd42cf59c47d`.
The complete deterministic output is in `k228_final_rebuilt/`. Its
`construction228.json` has SHA-256
`ed42e942ca11d29b57c427ec9b5d90514bfe22a3802751286973f80463fd0006`.

## Reconstruction checks

The repository-root CLI and the explicit-machine-and-sites CLI were executed
from an unrelated working directory, `/tmp`. The explicit-input execution also
used optimized Python, checking that the builder's validation does not disappear
when assertions are disabled. All eight output files were bytewise identical.
The final original-label machine, normalized original source, and transformed
source were also bytewise equal to the parent workflow's actual runtime inputs.
Changing either exact released input by one newline was rejected by its input
pin. The independent validation receipt is `builder_validation.json`.

The builder verifies complete binary transition tables, the exact state sets,
absence of dangling targets, the precise eight edits and two deletions, and
literal inversion of the final state renaming. It constructs and round-trips
the entire complete prefix-free source tree. Both complete programs have
boundary signature `(0,0,true)`; the two substituted fragments both have
`(0,0,false)`.

## Source theorem and contextual use

At the four exact occurrences recorded in the builder and receipt, replace

`((CD6,(CI5,CC2)),CI5)` by `(CI5,(CD6,CC2))`.

For every natural register file with `(R5,R6)=(a,b)`, each fragment terminates
normally, leaves `(R5,R6)=(a+b+1,0)`, and preserves every other register. Induction
on `b` proves the result: the original fragment transfers `b` units and then
increments once; the replacement increments before each conditional decrement,
including the final zero test.

The fragments have no escaping break or continue and cannot halt. The node
rules in the released `coq/tm/RM.v` therefore support replacement in all four
contexts and in the iteration of the whole root. This is equality of complete
macro effects, rather than equality of individual leaf-step graphs. The proof
is supplied in `k229_transfer/source_transfer_proof.tex`.

The source census changes from 5,125 to 5,121 leaf occurrences and from 6,660 to
6,656 decrement-guard cases. Both source trees have 212 distinct DAG nodes,
maximum depth 40, and maximum zero run 6. The logical-to-physical permutation
remains `[6,2,0,4,3,7,8,5,1]`.

## Complete initialization and invariant entry

An independent sparse-set tape interpreter executes the original table for
408,419 transitions and the final original-label table for 409,835 transitions.
The resulting complete state, head, and set of one-cells agree. Both endpoints
have state 84, head -5, marker -6, register header 176, 351 one-cells, physical
primary registers `[0,0,0,3,0,0,3,0,0]`, and 167 spare registers equal to one.
No boundary is imposed on either side of the tape. This independent result is
in `k228_startup_independent.json`; the interpreter is
`check_k228_startup.py`.

The initial logical register file is `[3,0,0,0,3,0,0,0,0]`, which is the released
`Prog230.v` definition `upd (upd regs0 0 3) 4 3`. The header lies 181 cells right
of the head, so the quantified runtime frame uses its natural gap parameter
`g=117`, since `181=64+117`. Both source trees have the same first leaf
`('000',CD8)`. Its zero path plus zero padding encodes the all-zero initial
instruction pointer exactly. The 167 spare blocks supply one distinguished
first spare and a finite tail of 166 blocks. Every certified non-halting instruction keeps
at least one spare block, and increment appends a spare block, preserving this
part of the invariant.

## Runtime review and proof scope

The parent workflow's final-table runtime certificate reports all 6,656 guarded
cases proved using the actual 456 rows, with 1,614,426 symbolic rule applications,
at most 415 rule applications per case, and at least 13 literal transitions per
case. The reference K230 certificate reports all 6,660 cases proved on its 460
rows. Neither report has unused rows. This audit inspected both completed
receipts and confirmed that their checker, symbolic-engine, and helper hashes
still match the executed source files; it did not rerun their full case sets.

The engine's universal rules are literal machine transitions, induction over
unary lengths for monotone same-state scans, and finite-list induction using four
one-block schemas rederived on the exact table in opaque exterior contexts.
The endpoints compare the complete tape and head, and each instruction has
positive duration. The proof-search limit of 4,000 symbolic rules per case
imposes no bound on registers, gap, spare-list length, or concrete runtime.

The fresh original-table runtime proof and the final-table runtime proof let the
source macro theorem connect the two literal blank-input machines directly.
This avoids an additional unverified identification between the released JSON
source and a Rocq AST: the reference table itself is the common endpoint.

The upstream theorem `Correct230.tm230_halts_iff_ZFC_inconsistent` connects that
exact K230 machine to `StandardZFC` inconsistency. The final mathematical chain
thus transfers its calibration to K228. There is no new K228 Rocq theorem in
this package and no claim that a local Rocq rebuild was performed. The ordinary
mathematical proof uses finite syntax, natural-number induction, finite-list
induction, and the referenced set-theory consistency reductions; it must not
be described as an inference from the unrestricted soundness of Rocq inside
ZFC.

No additional mathematical obstruction was found in this review. The practical
entry point for universal checking is `verify_runtime_k.py`; the imported cores
retain unused legacy executable drivers with earlier state-label assumptions.
Their executed proof functions are the ones whose hashes appear in the final
receipts.

## Attribution and reduction accounting

Glazer's compact K theory and the original K230 Rocq calibration are upstream
contributions. The present construction transfers and composes two previously
developed ProveIt state reductions. Two other savings from the ProveIt 243-to-235
chain were already incorporated into K230, and four are not claimed as
transferred. The complete eight-step accounting is in
`k228_transfer_accounting.md`.
