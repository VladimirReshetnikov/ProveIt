# Ordinary proof for the exact K217 table

The argument has five parts: inherited numerical calibration, unchanged source behavior after reassociation, the local state merge, quantified primitive execution, and complete blank initialization. The [intake reproduction guide](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-192-reproduction.md) retains the full submitted manuscript. This is a new exposition, not a copy of that manuscript. Every claim about fresh execution is subject to the status on the [candidate README](README.md).

## 1. The inherited dominated calculus

Use Cantor pairing `P(a,b)=(a+b)(a+b+1)/2+b`, implication `I(a,b)=4P(a,b)`, truth 0 and falsum 1. The native code alias `I(0,0)=0` is retained. The immediate parent admits the numerical row

```text
((C→U)→A) → ((A→C)→(B→C))
```

only when `U≤A`. All other rows, the literal gated seed bundle, MP and theorem-only GEN remain unchanged. The parent certificate derives the unrestricted row from these restricted instances. Its 3,728 proof nodes and 5,160 shared terms were checked by two forward implementations in Source149.

The restriction is justified for every natural assignment, including degenerate codes: implication numerically dominates each input, so a literal implication subterm U of A satisfies U≤A; U=0 does as well. Schematic substitutions instantiate universally quantified numerical theorems. They do not assume that arbitrary substitution or renaming is admissible in the entire native object calculus. Induction through the finite certificate, followed by replacement of each unrestricted axiom leaf, shows that the restricted and original calculi derive exactly the same natural codes.

The inherited common-input AX wire is `[c+3,z,y,x]`, giving `U=D+z`, `A=U+x`, `B=H+y`, `C=c`. The source constructs `Q_U(H)` with the incoming cache before y and x change its relevant values. It therefore emits only valid dominated rows, while retaining the bundle's numerical label/matrix coupling and gates.

Soundness uses theoremhood of the current formula, cache and accessible stack. Completeness uses a stronger command-block contract: from arbitrary top and stack with counter/cache zero, the block halts early or returns its theorem while preserving the stack and clearing those fields. The exact reset, ten-entry AX stack layout and selection/cleanup counts are supplied by the inherited compiler. Positive proof-list pointers drain. Padding a fixed refuting suffix R by a reset AX gives cofinally many candidate codes `P(3,P(1,P(1,P(Y,R))))≥Y`, so any finite starting cutoff is permitted. Combining this with the pinned native-calculus/ZFC calibration identifies source halting with a finite ZFC refutation.

No foundational calibration is inferred from a short machine run. The parent result and its hypotheses are explicit premises of this construction.

## 2. Three source reassociations

At prefix `11101001001110010`, identify five closed, halt-free factors D,A,B,C,E with 14,27,53,374,3682 primitive leaves. The transformation is

```text
(D, (((A,B),C),E))  →  ((D,A),((B,C),E)).
```

It is realized at current parent/child state pairs `210/188`, `213/210`, and `201/213`. Each participating decoder preserves its scanned bit and moves right; its rotated child has exactly one incoming edge and one logical subtree role. The expected role of that child is explicitly changed at each stage, and the complete decoder relation is checked against the new source.

The old and final sources contain the same 4,751 ordered primitive operations and operands. All guarded ordinal successor edges also agree, including both decrement branches and every break, continue and halt. Thus each source step preserves the correspondence of ordinal and the entire register tuple, for arbitrary natural values. Induction gives an unbounded source bisimulation. Closure does not assert termination: an infinite execution within a factor remains infinite under either association.

Only 94 primitive addresses change. The final source still has 203 distinct subtrees, depth 45 and maximum zero run 6. State 213 now represents `(D,A)` with rows `213/0=0R92` and `213/1=1R90`; existing rows `92/0=0R104` and `90/0=0R105` provide the continuations needed below.

## 3. The written-marker state merge

Let T be the [rotated 218-state table](unfolded218.native.tm), U the [final native table](k217.native.tm), and `phi(400)=69`, with every other state fixed. The old roles are:

| State | Read 0 | Read 1 | Sole incoming row |
|---|---|---|---|
| 69 | `0 R 105` | `1 R 31` | `53/1 = 1 R 69` |
| 400 | `0 R 104` | `1 R 31` | `224/0 = 0 R 400` |

Since neither is initial, every visit to 69 has marker 1 immediately left of the head, while every visit to 400 has marker 0. The immediately preceding transition writes this marker regardless of the initial tape.

Delete 400, redirect its incoming target to 69, and set `69/0=0L213`. On a read-one, the shared row already agrees in one step. On a read-zero at h, U follows one of two three-step blocks:

```text
marker 0: (69,h) → (213,h−1) → (92,h) → (104,h+1)
marker 1: (69,h) → (213,h−1) → (90,h) → (105,h+1).
```

The current zero and written marker are both preserved. Every other cell is untouched. These endpoints equal the old one-step endpoints in state, head and **entire tape**. Outside the pair, the transition rows are identical after applying phi to targets.

Concatenating the positive blocks simulates every old execution. Each mapped entry reestablishes the origin marker. Every finite old halt is a finite new halt, and every infinite old run produces infinitely many new steps. Conversely, determinism forces U to follow the same blocks from matching boundaries; no block halts internally and each has at most three transitions. Therefore U cannot halt while T runs forever. This proves halting equivalence on every binary initial tape from state 0, not from arbitrary initial configurations inside the merged pair.

Relative to the dominated parent, the final table changes nine retained rows and removes 400, with no new state. Relative to T, only `69/0` and the target of `224/0` change before the deletion. The canonical presentation is a verified bijective relabeling of the 217 remaining working states.

## 4. Runtime and blank initialization

Source equality and the local fold are useful separate theorems; neither alone establishes the complete blank-start result. The exact final table must implement each source primitive and reach a suitable source seed.

The 6,176 guarded primitive contracts use independent arbitrary natural register values and gaps and arbitrary nonempty finite spare lists. A decrement splits into zero and positive `1+n` cases. Every contract compares the full represented tape, including source address, header, zero padding, all registers, spare tail and infinite zero exterior. Literal transitions, unary induction and list induction justify the symbolic rules. Positive affine durations ensure that an infinite source execution gives an infinite binary execution; a finite derivation-search cap is not a bound on the represented values or runtime.

The complete blank prefix ends after 312,617 transitions at native dispatcher 84, head −5 and gap 80, with logical registers `[3,0,0,0,3,0,0,0,0]`, 130 one-valued spares and precisely 277 one cells. The control field is entirely zero, so this is the root frame rather than an intermediate dispatcher visit. Top, stack and cache are zero and theorem-safe; the candidate and additive counters 3 are allowed by cofinal completeness. Sparse, dense and canonical checks compare the complete support, not merely a clean-looking local window.

Composition identifies halting of these exact bytes with the existence of a finite ZFC refutation. Classical negation yields `blank nonhalting ↔ Con(ZFC)`. All finite constructions and natural/list inductions in this ordinary argument are formalizable in ZFC without assuming its consistency. No new exact-table Lean/Rocq theorem or internal PA proof is asserted.

## 5. Corroboration and the next target

Opening's independently constructed source matches this source byte for byte; its table is equal under the native-label cycle `188→213→210→188`. Its proof and complete startup are corroboration of the same saving, not an additional reduction. The previous primary/contextual K218 folds are different source-allocation arguments and cannot be added by counting removed labels. A 216-state result requires another proved compatible construction and its own complete runtime/startup evidence.
