# Further simplification: a 189-node arithmetic core

## New result

The earlier 367-node affine core contains 174 copies of one triangular-number
loop and four copies of a conditional-clear loop. Exact recognition and ranked
contraction leave **189 nodes: 188 tests and one halt, with 376 edges**.
This is an auxiliary proof representation, not a smaller Turing machine.

Unlike the preceding drain reduction, the new edge updates are not all affine.
They are short programs alternating existing affine matrices with two guarded,
total natural-number summaries. Expanding them into unrestricted polynomial
expressions would lose the crucial zero/nonzero distinction and can cause
expression blowup. Keep the guards and composition explicit.

`arithmetic_core.json` is 30,716 bytes, slightly larger than the preceding
29,381-byte affine graph despite having fewer control nodes. This is therefore
not a byte-compression or speedup claim. Its advantage is a reusable arithmetic
proof interface and fewer remaining control-flow tests.

## Exact triangular recurrence, including arbitrary scratch

At each recognized node the tested register is R6. Write x=R6, s=R1, y=R7.
The nonzero edge returns to the same node. The retained test first decrements
R6, then the exact affine matrix has the following effect:

    if x > 0: (x,s,y) -> (x+s-1, 0, y+x+s).

All other registers are unchanged. The matrix equality is checked coefficient
by coefficient, not by its dictionary index or a hash.

If x=0, the body is skipped entirely. In particular s is NOT cleared and no
triangular contribution is added. If x>0, put n=x+s, which is positive. The first
iteration sets the scratch register to zero and adds n to y, leaving x=n-1.
Subsequent iterations add n-1, n-2, ..., 1. Thus the exact pre-exit summary is:

    x=0: unchanged register file;
    x>0: R6=0, R1=0, R7=old R7 + T(old R6 + old R1),
          all other registers unchanged;
    T(n)=n(n+1)/2.

The increment is T(x+s), NOT T(x+s)-T(s). For example x=1,s=5 adds21, not6.
There is a genuine discontinuity in the formula at x=0: x=0,s=5 adds nothing
and preserves s. A scratch-zero invariant is unnecessary and is not assumed.

The universal proof uses the standard sum identity T(k+1)=T(k)+k+1 and
induction on k for the s=0 loop, preceded by the first nonzero iteration when
s may be arbitrary. It executes exactly x+s nonzero affine-core steps when
x>0, then one zero-exit step. When x=0, it executes only the zero-exit step.
The zero-exit matrix is applied AFTER this summary; it can modify any register.

This loop need not decrease R6 on its first iteration: arbitrary scratch s can
increase it. A naive induction claiming that every iteration decreases R6 would
be false. The correct argument separates the first iteration from the remaining
scratch-zero countdown. Equivalently, a two-phase well-founded argument handles
an initial nonzero scratch and then the natural countdown.

## Conditional-clear recurrence

The four other recognized self-loops also test R6. Their nonzero body decrements
R6 and clears R5, leaving all other registers unchanged. The pre-exit summary is:

    R6=0: unchanged;
    R6>0: set R6=0 and R5=0, preserve other registers.

It executes exactly old R6 nonzero steps and one zero-exit step. Clearing R5
unconditionally would be wrong for an entry with R6=0 and R5>0.

## Composition and halting preservation

Every removed node has a checked natural rank, strictly greater than the rank
of its zero-exit destination if that destination is also removed. Retained
nodes have rank zero. All 178 rank checks pass; maximum rank is7. Thus finite
termination of each arithmetic macro cannot hide an infinite chain of macros.

For each retained test, first choose the zero/nonzero branch using its actual
register value. On a nonzero branch, explicitly decrement that register BEFORE
executing the edge program. Then execute its affine update, the first summary,
its zero-exit affine update, and subsequent summaries and exit updates in order.
The certificate validator checks this whole literal path and instruction order.

Both local summaries terminate for ALL natural register files and consume at
least one affine-core step including their zero exit. Every retained core edge
also begins with one real test step. No halt is removed; summaries have no halt
in their bodies. A forward induction expands finite arithmetic-core halting
runs into finite affine-core runs. Conversely, determinism and the total local
summaries split an affine-core halting run into nonempty prefixes ending at
retained nodes; induction on original run length gives arithmetic-core halting.
The final register vector is preserved, not merely existence of a halt.

The initial node remains retained vertex0 with the identity entry matrix.
No register permutation, initial-value restriction, new halt, or hidden entry
normalization is introduced. Compose with the earlier drain-contraction and
source-to-canonical-graph adequacy theorems to recover the original endpoint.
These generic theorems are mathematical proof obligations here, not newly
kernel-compiled Lean or Rocq artifacts.

## Checked evidence and limits

The owned script `summarize_arithmetic.py` reads inert JSON only. It validates
literal matrix shapes, source labels, branch polarity, exact exit binding,
strict ranks, full retained-node partition and exact edge instruction lists.
All equality checks use full data, never a hash assumption.

- 14,418 local executions passed: all178 loops, x and s each0 through8, with
  unrelated registers nonzero.
- 554 complete retained-edge executions passed, including the core decrement.
- Ten other edge-regression inputs exceeded the10,000-step test budget. They
  are explicitly recorded as uncompleted, NOT passed, failed or divergent.
  Composed triangular operations can grow values extremely quickly. The finite
  certificate checks still completed for every edge; the universal argument
  does not depend on bounded simulation of those ten cases.
- Four adversarial certificates were rejected: wrong summary kind, invalid
  exit rank, omitted core-decrement contract and reversed operation order.
- Explicit regressions distinguish T(x+s) from T(x+s)-T(s), and preserve the
  zero-entry scratch register.
- Optimized Python is rejected before running checks, to avoid disabled asserts.

Input affine JSON SHA-256:
`718e70b8896200396d50d40aea13df24e326771afd475893c8fd6c90efac5145`.
This is provenance only, not a proof premise. See the preceding structural
report for its full source and drain checks. The current-main review independently confirmed that p215Nodes, p215, t215 and
tD literals are unchanged at aa66d0a33f1f8237a348899eb8095b045a502832 relative
to the prior53269bc baseline; see CURRENT_TREE_BINDING.json. The maintained
source-equivalence dependency changed to the ordinary lane, so this alignment
does NOT imply all proof dependency files are unchanged.

## Practical priority

For a pair already having identical canonical graphs, direct full graph equality
remains simpler than running this extra contraction pipeline. The new result
is most useful when comparing variants that implement the same arithmetic with
different transfer-loop control flow, or when proving source-level arithmetic
composition once instead of repeatedly calibrating small steps. It supplies
concrete macro candidates; it does not yet establish equivalence to an additional
215-state candidate, reduce the Turing-machine state count, or measure a faster
proof build. No repository code was pushed or original formal endpoint weakened.

## Reproduce

Run `python summarize_arithmetic.py` in this directory. It requires only the
Python standard library, imports no received scripts, and writes its complete
finite-check audit and arithmetic-core certificate artifacts.
