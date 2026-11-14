# Model-uniform PA194 formula-shift constructor steps

This package supplies fixed finite candidate-PRA code expressions for the
remaining source formula-shift cases after atoms: `verumCode` and `falsumCode`
handle truth and falsity, and `binaryCode`/`unaryCode` rebuild conjunction,
disjunction, universal and existential formulas from their already-shifted
children.

The eight checked theorems prove the corresponding equations in every
candidate-PRA model whose arithmetic reduct satisfies IΣ₁, including
nonstandard formula and child codes. The conjunction, disjunction and
quantifier theorems require internal well-formedness of the child formulas.

The source was checked against the ordered source and term-graph overlays;
all printed theorems report `[propext, Classical.choice, Quot.sound]`, without
`sorryAx`. The full nested standalone replay remains pending.

The compound constructors take shifted children as inputs. A uniform history
and dispatcher code that recursively computes those children at all internal
indices has not been built here. Full formula shift, nonstandard proof
compilation and PA194 machine calibration remain open.

From the repository root, set `IPRA_FOUNDATION_OVERLAY` to the audited current
Foundation object overlay and `IPRA_LEAN_OVERLAY` to the pinned audited
project object overlay, then run
`bash Computability/BusyBeaver/Research/PA/pa194-compound-shift-step/check.sh`.

An independent suffix replay recompiled the constructor-step module in a fresh
output directory against the separately rebuilt vector/atom objects and the
audited prerequisite overlays. It reported the same axioms with no `sorryAx`;
the full prerequisite chain was reused.
