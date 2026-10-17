# Audit of the binary countdown extension

This audit covers `binary_loop_experiments/trace_cutpoints.py`,
`check_countdowns.py`, and `screen_remaining.py`. It checks the mathematical
meaning of the implementation and records a separate continuous literal
control for one newly accepted guarded macro. No complete smaller machine
was found.

## The diagnostic is a restricted prefix search

The trace observer is inserted into the inherited strict executor through
its AST. Apart from allowing an explicitly supplied initial symbolic
configuration and adding that observer, the literal, scan and box-excursion
rules remain unchanged. The observer records the working state, head-side
flag and canonical entire left/right tape description, erasing only the
plain box's primary offset. The finite spare suffix remains existential,
as in the proved box-composition relation.

These tapes describe a complete interface relative to the current head.
They do not separately record an absolute head coordinate. Recurrence is
therefore understood up to translation and the admissible spare suffix,
not as equality of two absolute configurations. The translation-equivariant
version of `binary_countdown_acceleration.md` is sufficient.

The positive-selection policy intersects the **original** input interval
when a current register value is undetermined. Since all previously proved
steps hold on a superset, they remain valid under this stronger premise.
The complementary branch has not thereby been verified. A repeated shape
with a decrement vector is only a proposed loop; independent universal
replay and a preserved invariant are required next.

## The universal body and zero-exit checks are sound

Let a be the prefix's current primary offset and d the proposed cycle
offset. The local replay reparameterizes the current values as v, erasing
the old offset from the box notation. This is a change of symbolic
coordinates, not a physical reset.

For an intermediate old ledger offset b, the current value is
`v_i+b_i-a_i`. Its nonnegativity requires `v_i>=a_i-b_i`. Positive guards
similarly require `v_i>=1-(b_i-a_i)`. The invariant extractor uses exactly
these inequalities. On the countdown register, it rejects any requirement
stronger than v_r>=1, so the final positive iteration is included. A zero
guard on the countdown register is rejected in a uniform positive body.
A zero guard on another register fixes its cutpoint value; it is admitted
only when that register's net cycle change is zero. Growing noncounters
retain only lower bounds, so d_i>=0 preserves those bounds. The invariant
therefore also holds at the zero boundary after the last positive cycle.

The body is then actually replayed with counter interval [1,infinity) and
the preserved invariant, with unknown guards rejected. It must return to
the same complete relative interface with exactly d and positive literal
progress. A separate replay at counter zero must reach a complete clean
dispatch frame. Its PC, affine gap, all nine primary values, state and
head-side flag are checked. A rejected or repeated abstract zero-exit
interface is not treated as a halting or nonhalting proof.

If z is that zero-exit offset, composition after the original prefix has
the exact primary matrix

`output_i = R_i + d_i*R_r + a_i + d_i*a_r + z_i`.

The implementation uses this formula with d_r=-1 and nonnegative other
components. The source comparator requires the same complete PC/gap and
equal affine rows after justified substitution of initial singleton
coordinates. Its source frontiers are the independently proved countdown
summaries and retained exact finite prefixes.

## Full guarded-domain coverage is a separate obligation

A universally valid local body does not by itself justify applying it to
the whole original source case. The code separately checks:

1. The entire original entry interval product is contained in the selected
   interval product recorded **before** the cutpoint. Thus no positively
   selected prefix branch excludes an original input.
2. The original intervals shifted by the prefix offset a are contained in
   the preserved local invariant J.

These are the correct directions of interval inclusion. They rely on the
sound observed prefix retained by the trace diagnostic; they do not amount
to a second independent replay of that prefix. A local-body result with
failed prefix coverage is not promoted to a source-case certificate.

## Remaining-case screening

Before every ordinary source-block check, `direct` restores the intended
oracle and its per-case bound function. `source.check_one` then installs
that case's current bounds. This prevents a preceding local replay's
temporary invariant from leaking into the next direct check.

The baseline tracks every literal or scan row lookup. An unchanged baseline
trace that never visits the deleted working state retains its exact witness:
it never takes a changed incoming transition before its endpoint, and all
opaque box-support rows are frozen. The deleted state is distinct from
dispatch and from protected box states. All affected cases still need
direct comparison or a new complete countdown/source certificate. Every
new selected trace is subjected to the same prefix coverage checks.

There were 51,290 selected first-failure traces. They yielded 9,253 proposed
countdown recurrences. All 9,253 proposed bodies passed universal replay;
9,239 had a checked clean zero exit. Of those, 9,101 covered the complete
original entry domain. There were **138 full source matrix/PC/gap matches**,
all with prefix coverage. These are real new guarded-macro successes.

Continuing those 138 fold recipes required 568 direct checks and 58 fresh
countdown candidates over five rounds. Another **43** complete guarded
macros passed, giving **181** in total. Nevertheless, 123 recipes met a
further rejection without an admitted countdown and 15 met a source-endpoint
rejection. No recipe passed every applicable case. These checker rejections
are not lower bounds or proofs that the mutations cannot be calibrated by
some other relation.

## A concrete new macro, with continuous literal controls

For fold **78 -> 11**, source case **8231**, the initial PC is
`111010010111111`. Its preserved binary loop invariant permits arbitrary
natural primary values. One positive cycle moves one unit from physical
register 8 to physical register 7; the separate zero exit reaches PC
`111010011` with the same affine gap. Its total primary effect is

`R'_7=R_7+R_8`, `R'_8=0`, all other primaries unchanged.

The original source reaches exactly that PC and matrix in `3*R_8+2`
successful source steps. The binary cycle is justified for every positive
counter, and its zero exit for counter zero. This is the essential
unbounded argument; the following tests are independent regression controls.

`binary_countdown_literal.py` runs **16 continuous literal binary probes**
from prepared complete input frames. They cover counter values 0, 1, 2 and
5, two gap paddings, two distinct initial head locations, and both empty
and nonzero spare lists. No binary step is replaced by an oracle, scan,
reset, or summary. All complete final one-cell sets match the source
matrix and PC, including exactly R8 additional zero spares. Omitting those
spares fails the comparison in the 12 positive-counter probes. The runs
total **42,008 literal binary transitions**; the independently executed
source runs total **128 successful source steps**. All observed heads also
return to their initial coordinates, although the proof only needs the
translation-equivariant interface.

These prepared-frame probes are not blank-start runs. Fold 78 -> 11 itself
is subsequently rejected at source case 8227 by the remaining checker, so
the displayed local macro must not be presented as a successful 251-state
consistency machine.

Run the independent controls with
`python proof_audit/binary_countdown_literal.py --output <temporary.json>`.
The default destination is `binary_countdown_literal.json` alongside the
script; the receipt records its code and pinned source/table hashes.
