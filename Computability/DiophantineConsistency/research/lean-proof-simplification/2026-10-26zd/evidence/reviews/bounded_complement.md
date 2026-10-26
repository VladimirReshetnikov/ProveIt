# Direct bounded-complement cancellation

Status: integration candidate; core arithmetic checked separately.
Snapshot: 89226e3921bce3e8949fadd12d3efb6914c7630c.

## Exact change

In CurrentTileColors2011.facts_horizontal_colors and facts_temporal_colors,
replace each final four-line block (two destructurings of tile_bounded,
rewriting the two word values, and omega) by a direct application of the
existing mathlib theorem tsub_right_inj. No new helper or import is added.
The full module goes from 104 to 100 physical lines: eight deleted, four
added, four net lines removed. Both public theorem headers are byte-identical.

The proof uses only east/west bounds for the horizontal edge and south/north
bounds for the temporal edge. Both guards remain explicit. The equations
are composed as left label inverse, existing copied-word equality, right
label. A bound a < cap+1 implies a ≤ cap via Nat.le_of_lt_succ.

## Why this survives earlier proposals

The assumed binaryWord_congr and copied-field APIs already yield the word
identity used here. This change addresses only the subsequent cancellation
of bounded natural complements. It does not re-propose word congruence,
color-fiber classification, or coordinate transport. This is deliberately
an optional four-line local cleanup, not a new architecture or performance
claim.

## Mathematical audit

For a,b ≤ c, applying x ↦ c-x to c-a=c-b gives a=b by
Nat.sub_sub_self. The core-only BoundedComplementCore.lean checks this exact
reason in Lean 4.32.0 and prints [propext] as the complete axiom list.
Without the guards, 255-256=255-257 while 256≠257, also kernel checked.

The production statement of tsub_right_inj was inspected at
https://github.com/leanprover-community/mathlib4/blob/v4.32.0/Mathlib/Algebra/Order/Sub/Basic.lean#L89
and has the required form

    theorem tsub_right_inj (hba : b ≤ a) (hca : c ≤ a) :
        a - b = a - c ↔ b = c

It requires ordered cancellative additive structure, supplied by Nat.
Current imports already include Mathlib.Tactic through the Wang tile data
chain. No full mathlib/source-module replay has been performed here; the
small core audit must not be reported as an integration build.

## Application

From the pinned repository root, use git apply --check bounded_complement.patch
then apply in a disposable checkout and compile the changed module and its
existing checks. The archive also contains the complete candidate module.
