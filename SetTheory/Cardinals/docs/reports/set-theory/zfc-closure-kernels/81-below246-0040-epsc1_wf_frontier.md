# EPSC1 and an internally well-founded interpretation: the remaining gap

EPSC1 alone remains an open theory-reduction direction in this work. No
new implication from EPSC1 to a ZFC-strength interpretation is proved
here, and no impossibility result for such an interpretation is claimed.
The concrete missing step is a uniform way to assemble enough internally
well-founded witnesses using only one ordinary matrix parameter.

The starting separation and its pure inner class belong to manuscript
36, not to this note. Its preserved `sections/one_parameter.tex` is in
the `zfc_small_machine_research_2026-10-16 (2).zip` arrival at
`4e720ccbbfaa836b95be3b2f3f268a737b48c6d1`, reconciled in
[the collection's source-36 discussion](../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md).
That report already explicitly constructs the common pure class `P` of
its three components and the membership-preserving class bijection
`x ↦ check(x)` from the ambient ZFC universe to `P`. It explicitly
distinguishes that fact about its particular interpretation from a
calibration of EPSC1 in every model.

## What the separation does and does not rule out

EPSC1 allows matrices with input `x`, output `y`, and at most one
additional ordinary free parameter `p`. Bound variables and formula
complexity are unrestricted. Its subset-bounded positive hull is seeded
by all empty objects and has global output support.

Source 36 gives a ZFC-definable class interpretation with Extensionality,
raw irreflexivity, Empty Set, Union, Power Set, Infinity, full Separation,
parameter-free Replacement, the stated set-indexed Choice principle, and
every EPSC1 instance, even with native equality. Two non-pure objects in
different components have no common membership container. In particular
Pairing and specified EPSC2 and one-parameter Replacement instances fail.
Its existing hereditary-saturation cut is the whole structure and still
fails Pairing. This is a deductive separation; it does not refute another
interpretation of ZFC.

For precision, **this source-36 model also fails coarse mixing**. The
support identity

```text
supp(t) = ⋃{supp(u) : E(u,t)}
```

implies `y⊆E b → supp(y)⊆supp(b)`. Nonempty objects supported in
different components have no common subset bound either. The stronger
construction claimed in the newly arrived, not yet fully reviewed
unary-closure report is a separate model and supplies no premise here.

## Why the checked TW closure theorem does not settle EPSC1

For an arbitrary first-order membership structure, let

```text
TW(t) := t is transitive and every represented nonempty subset of t
         has a membership-minimal element;
WF(x) := ∃t (TW(t) ∧ x∈t).
```

Only represented subsets are quantified over. This is internal
well-foundedness and must not be replaced with external well-foundedness
when considering nonstandard models.

[`WellFoundedPart.lean`](../../Lean/BusyBeaver/ZFC/WellFoundedPart.lean)
proves closure of `WF` under represented sets of WF members using
Pairing, Union, the literal intersection Separation instance, and GIC for
the fixed equality-free matrix

```text
R(x,t) := TW(t) ∧ x∈t.
```

The proof collects a represented family of TW witnesses, unions that
family, and adjoins the original set. Its premises are available in the
existing CP+GIC quotient, but have not been derived from bare EPSC1.
Three exact gaps prevent simply reusing it:

1. The witness relation has arbitrarily many TW witnesses per input.
   No object bounding all these outputs by raw subset has been supplied.
   Consequently its GIC instance cannot be replaced by an EPSC1 instance
   merely because the displayed matrix has no extra parameters.
2. The proof of minimality through a TW set forms `s∩t` for independent
   represented objects `s,t`. The existing theorem obtains this from
   actual Separation. Bare EPSC1 has not been shown to provide full
   Separation with arbitrary parameters. Taking a constant-output
   matrix for membership in both `s` and `t` uses two ordinary parameters
   unless an independent coding construction is supplied.
3. The final step forms `u∪{a}`. Pairing supplies `{a}` and the binary
   combination. Those are precisely among the operations missing in the
   source-36 ambient model. Assuming them would change the candidate
   theory instead of deriving the proposed interpretation.

Choosing a unique canonical TW witness might repair the first fiber
bound: a functional output is subset-bounded by itself. It still requires
a proof of existence and uniqueness inside the candidate, enough
activation to collect the witnesses for a given represented input set,
and the finite set constructions needed afterward. Invoking an existing
rank, ordinal, transitive-closure recursion, or a graph coding theorem
that already uses Pairing or Collection does not supply those missing
resources.

The pure copy in source 36 therefore shows that its particular
counterinterpretation is compatible with a successful inner class, but
does not establish that the same first-order internal cut works in every
EPSC1 model. A useful next breakthrough would be an exact one-parameter
instance deriving a common container or canonical witness for two WF
objects, with all activation and output bounds verified. Until such a
lemma is available, this route has no calibrated replacement for the
current theory row and no measured machine saving.

## Batch154: coarse bounds still do not supply Pairing

Local source39 strengthens the source36 counterinterpretation. Its hereditary
one-index support model has Extensionality, irreflexivity, least exact unary
hulls, and finite common membership, subset and transitive bounds, while exact
Pairing still fails. Its hereditary-purity quotient is the entire bad model.
Thus coarse common-container repairs alone do not establish that interpretation.
The internally well-founded part still contains the ambient pure universe;
the remaining two-WF-object question above is not refuted.

The same report proves that adding exact BinaryUnion to EPSC1 permits the
full extensional EPSC interpretation. Over EPSC1, BinaryUnion and exact
profile Pairing imply each other. The proof packages finite pure parameters
inside one pure object and keeps the actual matrix's single-parameter budget.
These are ordinary mathematical results; the displayed formula/DAG counts
exclude label payload, tuple operations, proof search and initialization.
See the independently reviewed host dossier
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-154-source-39.md`.
No new calibrated binary implementation follows from this repair.

