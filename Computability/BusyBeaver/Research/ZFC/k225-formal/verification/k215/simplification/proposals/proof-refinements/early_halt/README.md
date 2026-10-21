# Early-halting stack selection: a checked compiler simplification

## New result and exact scope

`EarlyHaltSelection.v` and `NativeSelection.v` compile in Coq 8.18.0, their
four printed assumption reports are closed under the global context, and
recursive `coqchk` passes. The fresh commands, input/output hashes and logs
are in `verification/receipt.json`. A second build also compiles
`K215SelectorAdapter.v` against the exact production `K215F.cmd`, `xstep`,
`exec`, and `ax_stack`, with all eleven modules in its small dependency
closure freshly compiled and recursive `coqchk` passing. Its two printed
assumption reports are closed. See `production-verification-final/receipt.json`.
This is **not a replacement of the maintained compiler proofs or a rebuild
of the complete binary-machine/ZFC endpoint**.

The result is distinct from the three incoming proposals at snapshot
`aa66d0a33f1f8237a348899eb8095b045a502832`: those supply normalized/balanced
source certificates, decoder certificates, axiom transport, and concrete
zero-credit scheduler proofs. None of their inspected calculus/compiler
notes supplied this generic early-halting selector.

## The exact theorem

Write `P(x,w)` for a stack push, and require only

    unP(P(x,w)) = (x,w).

The state is `(top, stack, counter, cache)`. NIP first tests the **old cache**
for code 1; it halts if that test succeeds, otherwise it pops one head into
the cache. DROP pushes the old top and sets the top to the unchanged cache.
These are the literal production command shapes.

Let `rows=[x0,...,x(n-1)]`, with `j<n`. Put a final explicit zero below these
rows and retain an arbitrary numeric tail W. Then

    NIP^(j+1); DROP; NIP^(n+1-j)

from

    (G, pack(rows ++ [0], W), D, H)

**either halts early or returns exactly `(xj,W,D,0)`**.

The theorem is valid for arbitrary natural G, D, H, W and row values. It
requires no theoremhood, nonfalsity, well-formed-formula, or fresh-variable
hypothesis. In particular, some of the rows or G may equal 1. Such a value
may cause an early halt, which already satisfies the compiler's contract.
The arbitrary initial cache H may also equal 1. The counter D is preserved
exactly by the checked adapter.

The first `j+1` pops leave xj in cache. DROP makes xj the top and pushes G.
The remaining `n+1-j` pops remove G, the remaining rows and the final zero.
If no alarm occurs, the cache is zero and the original W remains. The
command never pops an entry of W. The final zero is loaded but never
subsequently tested by this block. No injectivity of numerical stack
encodings beyond the stated inverse law is used; `P(0,0)=0` is harmless.

## Why this simplifies the actual K215 completeness proof

The maintained compiler already uses the contract

    exec(block, (T,W,0,0)) = None
    or exec(block, (T,W,0,0)) = Some(X,W,0,0).

Its exact AX stack contains, in pop order,

    rho1, rho2, rho3, rho4, rho5, rho6, growG, rho8, GEN, saved_old_top.

After DISCARD, `saved_old_top=0`. The new indexed theorem therefore handles
all eight axiom selectors with indices 0 through 7. Generalization selects
index 8 of the same nine-row list; the existing `DROP; J; NIP` setup makes
the pre-AX saved top zero there as well. The gate G may be arbitrary.

The current implementation instead unfolds each selected block through
`xrun` and discharges nonfalsity premises on all skipped rows and on the
gate. Those premises prove that the branch returns normally, although
normal return is stronger than the declared compiler contract needs. One
inductive selector theorem replaces the repeated selection-path arguments.
The analogous `drain_prefix` theorem can handle a bundle selector with the
weaker early-halting contract too.

**Do not delete every nonfalsity lemma globally.** Exact-return routines,
other callers, and semantic soundness may still need them. The claimed
removal is limited to the selector proof path. Keep the current exact
`discard` theorem initially; the first integration need only replace the
eight leaf-selector proofs and the GEN extraction tail. Retain public
compatibility lemmas if downstream files use them.

Current leaf proofs are already written using a compact `leaf_tac`, so
this result does not by itself prove a net reduction in total source
lines or kernel time. It removes repeated proof obligations and makes
future changes to the AX row list easier to justify. A compiler rebuild
and proof-object/time comparison would establish any performance gain.

## Checked concrete production adapter

`K215SelectorAdapter.v` supplies the explicit injection of the two-command
language into `L1_CompPerm.cmd`, the required step and execution equality,
a literal `SELECT_word` equality, the exact nine-row AX stack view, and
`select_AX_row`. These proofs are now compiled and kernel-rechecked
against the actual production command definitions. The five production
files were verified byte-for-byte against their GitHub blobs at the pinned
commit; three receive only the `Stdlib` to `Coq` import-prefix adjustment
for Coq 8.18. No executable definition was changed. The inherited
optimized `DomRho8` proof from the incoming Checked Simplifications
packet supplies its existing public API, and was also freshly compiled.
All source provenance is recorded in `upstream/provenance.json`.

The remaining integration task is to replace leaf extraction by
`select_AX_row`, retain the normal-return/discard setup, and recheck the
existing endpoint. The compiled adapter proves its own actual-command
theorems; it does not replace the old `leaf_tac` or full `build` theorem
in the maintained repository.

The target source files at the pinned snapshot are:

- `Computability/BusyBeaver/Research/ZFC/k225-formal/rocqperm/L1_CompPerm.v`:
  `xstep`, `blk`, `leaf`, `leaf_tac`, `blk_r1` through `blk_r8`, `blk_gen`.
- `Computability/BusyBeaver/Research/ZFC/k225-formal/rocqperm/EnumPerm.v`:
  the exact `ax_stack` order.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/EnumPerm.lean`:
  `Contract`, `leaf`, `build`, `gen_contract`, and the repeated
  `rho1_ne` through `rho8_ne`/`growG_ne`/gate nonfalsity obligations.

## Exact client-integration statements (not yet compiled)

The maintained `leaf k a b c u` uses one-based k. Its extraction suffix
is exactly `SELECT (k-1) 9` for k=1 through 9: the two pop counts are k
and 11-k. Thus the intended single replacement lemma is

    Lemma blk_leaf_by_selection a b c u j X :
      u <= a ->
      nth_error (AXRows a 0 b c u) j = Some X ->
      blk X (leaf (S j) a b c u).

Its setup uses the existing exact `discard`, `exec_J`, `ex_ax`, and
`add_sub'` lemmas; the resulting state is exactly

    (gate a b c, ax_stack a 0 b c u 0 W, 0, 0).

Apply `select_AX_row` to that state, retaining its disjunction rather than
choosing `right` in advance. The eight current `blk_r1` through `blk_r8`
then instantiate j=0 through 7 and discharge `nth_error` by reflexivity.
The domination premise u<=a is retained for `rho8`; this result removes
selection-path nonfalsity obligations, not that source-calculus premise.

For `blk_gen`, retain the existing split on the child block's result. If
it returns `(X,W,0,0)`, the prefix `DROP; J i; NIP; AX(i;0,0)` reaches

    (gate i X i, ax_stack i X X i i 0 W, 0, 0).

The remaining literal suffix is `SELECT 8 9`, so instantiate
`select_AX_row` with a=i, h=X, b=X, c=i, u=i, j=8. Its row is `wal i X`.
This preserves possible early halts in the extraction suffix.

These statements specify the intended patch at the existing client
boundary. The production adapter and `select_AX_row` are kernel-checked;
the proposed `blk_leaf_by_selection`, rewritten `blk_gen`, and resulting
full endpoint have not been rebuilt in this packet.

## Verification and reproduction

With Coq 8.18.0 on PATH and a fresh output directory:

    python3 build.py --output /tmp/selector-fresh
    python3 check_numeric.py

The first build compiles both standalone files and runs recursive
`coqchk` on them. The production adapter can be rechecked, including all
eleven bundled dependency sources, with:

    python3 build_production.py --output /tmp/selector-production-fresh

No network or third-party Python package is needed. All small production
and inherited proof sources required by this second build are included.
Use `--coqc` and `--coqchk` to select executables if required. Any required
COQLIB/OCAMLFIND_CONF environment belongs to that toolchain installation.

The finite numeric regression checks 11,502 cases: 10,326 early halts and
1,176 exact returns. It tests numeric zero aliases, arbitrary small tails,
untouched counter 7, and that no execution pops below its explicit prefix.
It also checks a counterexample showing why a nonzero bottom sentinel
cannot replace the zero while retaining the zero-cache conclusion. These
finite checks are corroboration; the all-natural result is kernel-checked.

Independent internal reviews from the machine-reduction and proof-
simplification workers agree with the theorem and its integration scope.
Their findings are summarized in `independent-review.md`.

## State-count boundary

This refactor changes a proof of the command compiler. It changes no
published source program, binary transition, startup frame, or state
count. It gives no 214-state construction or state lower bound.
