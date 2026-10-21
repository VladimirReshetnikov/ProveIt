# Review of the transfer compiler and MP-first protected-tail theorem

This is a read-through of the ordinary arguments in the pinned repository:

* `candidate-k215/alternatives/direct-transfer/proofs/transfer_compiler.md`;
* `candidate-k215/alternatives/mp-first-transfer/proofs/permuted_credit.md`.

Both arguments are sound as conditional source/command-level theorems. They
do not by themselves prove that a new binary table implements the commands
or reaches the required startup frame.

## Transfer compiler

I independently traced the structural blocks against the stated commands.
The AX stack has ten entries: eight logical rows, the generalized cache, and
the saved old top. All but the saved top are non-1 codes. The full bundle is
also an implication code or zero. Those tag facts justify every guard claim.

For H=AX(0;0,0);S^11, after ten shifts the old top is cached and the old
stack is restored. The eleventh shift tests precisely that old top, then
returns the old top unchanged with one old stack head cached and removed.
It does not reproduce old NIP's incoming-cache guard; the proof correctly
uses this different contract. PUSH=AX(0;0,0);S^9;MP(0) leaves the old top
saved and forces MP failure because the cache has quantifier tag2 and the
constructed implication has tag0. DISCARD resets arbitrary incoming top
without touching its old stack. The empty J(0) case is necessary to avoid a
successful zero-alias MP and is explicitly included.

The axiom selectors count their residual generated heads correctly. In the
MP block, building the major before the minor leaves the stack in the order
needed by the two shifts. The successful MP's extra zero is exactly removed
by the final AX and eleven shifts; if the desired result is1, the final
shift halts. The GEN block deliberately moves the proved formula into cache
without testing it before AX resets the cache, so its stated contract even
covers a formula of code1. No inductive compiler step assumes the arbitrary
input stack is a theorem stack.

The right-nested field encoding with an outer successor at continuation
boundaries correctly compensates for the scheduler's decrement. Re-encoding
S and MP to the MP-first tags does not change the abstract blocks. The
cofinal shell AX(0;1,Y) retains selector2 and therefore has the displayed
candidate number P(2,P(Y,P(1,R))). This is at least Y. Its AX resets the two
registers required by the universal refutation block. Positive residual
proof pointers strictly decrease, so every sufficiently large chosen
candidate is eventually reached unless the machine has already halted.

## MP-first credit theorem

The recurrence W(n) is correctly indexed for MP=0, S=1, AX>=2. If
unpair(n)=(a,y), the respective continuation pointers are f(y), y, and
f(f(y)), where f is right projection. Every positive pointer r recursively
uses candidate r-1, which is strictly smaller than n. Hence each finite
candidate word has at most n+1 commands and its continuation loses at most
its pointer value under conservative weights (0,-1,10).

The Cantor order lists f as [0],[0,1],[0,1,2],... . Prefix nonnegativity
therefore pulls back through f and f composed with itself. Applying this to
g(r)+1, rather than g alone, is essential: B(2)=-1. The invariant
B(j)+j>=0 supplies exactly the nonnegative prefix sums used by the proof.
On a diagonal of index s>=2 the first s-1 candidates are AX, then S, then
MP. The bounds 9k for complete AX prefixes, 8s-9 through S and 7s-9 through
the final MP are valid and nonnegative. The recursion only requests indices
at most s-2<T_s in that use, so the induction is not circular.

At cutoff1 the initial words S,MP have minimum balance -1, and all following
whole diagonals are prefix-safe. Thus one explicit theorem head is exactly
the required conservative credit. The ten theorem heads of the proposed
AX bootstrap leave nine permanent protected heads above the arbitrary tail.
Before any actual S step the explicit prefix has at least one head: after
its cost-1 the credit invariant still has nonnegative length. Therefore no
nonhalting transfer ever reads the arbitrary tail. The numerical zero-list
alias does not invalidate this reasoning: it uses an explicit representation
P(x,w), whose exact inverse supplies the represented head and tail, without
claiming that the represented list length is unique.

The same weight proof covers the composite S' because its nonhalting stack
effect is identical. Its extra top=1 guard is sound whenever the top is a
theorem. The universal compiler's auxiliary blocks retain their stated
calculations because their intermediate top values are generated gates,
implication codes, or quantifier codes; the extra guard can only cause a
permitted successful early halt at a theorem or an arbitrary input encountered
in the universal completeness contract.

## Required premises for any new direct MP-first machine

Before applying these results to a new binary candidate, separately establish:

1. Its exact source has MP selector0, single-guard S selector1 and AX
   selectors at least2, with the stated payload order and command equations.
2. Its all-natural binary primitive simulation covers that exact source.
3. Its own blank execution reaches the claimed source-interior frame.
4. A synthetic AX prefix on the same new source reaches exactly that frame,
   including all logical registers and continuation control; the inherited
   suffix contract then supplies ten theorem heads over the stated tail.

Earlier 68,442-step and ordinal55 measurements belong to the earlier
composite table. They must not be silently reused for a new direct table.
Once these premises hold with next-candidate cutoff1 and empty proof pointer,
the safe protected-prefix invariant gives soundness, and the universal
compiler/cofinal shell gives completeness. The inherited numerical-calculus
calibration then supplies the desired ZFC consistency equivalence.
