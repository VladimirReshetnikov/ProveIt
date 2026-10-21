# Four explicit rho8 schemas suffice

This is a checked extension of the implication proof simplification. It is
separate from the compatibility patch; the checked generic core and the
existing numerical adapter are unchanged.

## Statement

Let `I : A → A → A` be any binary operation on any type. No injectivity,
formula decoder, order, distinguished truth, or equality law is required.
Write

`ρ(a,b,c,u) = I(I(I(c,u),a), I(I(a,c),I(b,c)))`.

For any predicate `T : A → Prop`, assume modus ponens and the following
four axiom schemas, with every displayed variable universally quantified:

| Shape | Axioms supplied to T | Path from the first argument to u |
|---|---|---|
| Same | ρ(u,b,c,u) | empty |
| Right | ρ(I(x,u),b,c,u) | R |
| Left-left | ρ(I(I(u,x),y),b,c,u) | LL |
| Left-left-right | ρ(I(I(I(x,u),y),z),b,c,u) | LLR |

Then `T(ρ(a,b,c,u))` for every `a,b,c,u`. The four schemas are finite in
number; each schema still has arbitrarily many instances. There is no
claim that four schemas or maximum path length three is minimal.

`FourShapeImplication.all_of_four` is the direct interface. The same file
also exports composition, distribution and unrestricted rho8 for the
equivalent four-constructor `Allowed` relation.

The relation is deliberately not assumed closed under every implication
context. Consequently this result does not follow merely by instantiating
the more general-looking dominated-relation interface: the finite proof
must be specialized at its actual guarded leaves. All nine leaf/guard
witnesses are explicitly listed in `four-shapes.json`:

- R at b1;
- LLR at b31;
- LL at cd62, cd64 and cd67;
- empty at b0, cd34, cd82 and the auxiliary seed.

The intermediate conditional helpers pass these exact witnesses unchanged.
There are no other numerical or structural side conditions. A temporary
proved element τ is obtained from ρ(a,a,a,a), so no truth axiom is used.

## Exact numerical-calculus adapter

`KCodeFourShape.lean` defines `CFour` using the existing numerical
representation and all of C222's other rules:

- the existing truth rule `CFour 0`;
- modus ponens and generalization;
- rows r1–r6 and rG;
- the bundle with its original two guards `c ≠ a` and `c ≠ b`.

Only r8 is replaced by the four explicit constructors `r8same`,
`r8right`, `r8ll`, and `r8llr`. The truth rule is retained in this
adapter. The generic four-schema theorem itself needs no truth premise.

`cfour_iff_c222` states `CFour n ↔ C222 n` for every natural-number
code n, including codes with no intended formula interpretation.
`consistent_iff` specializes this to nonderivability of the existing
falsity code F. Thus the already established calibration of C222 transfers
by composition. This is equality of raw-code derivability, stronger than
an equiconsistency-only claim.

Only the propositional r8 interface is free of arithmetic side conditions;
the full code calculus still contains its original numerical operations
and bundle guards.

## Verification and reproduction

The four-schema abstract source imports `Init` only and was compiled
with Lean 4.32.0. The four public theorem axiom reports are empty.
The independent receipt is
`proof_simplification/clean-four-shape-final/receipt.json`.
The numerical adapter was checked in a fresh 13-module closure; its
rho8_all, cfour_iff_c222, and consistent_iff also have empty axiom reports.
A separate direct proof-term Rocq port, FourShapeImplication.v, passed
coqc 8.18 and recursive coqchk. All three exported generic theorems are
closed under the global context. Its receipt is
proof_simplification/clean-rocq-four-final/receipt.json. The Rocq port covers
the abstract four-schema theorem; the numerical CFour adapter is Lean-only
in this packet.

Run

```sh
python3 specialize_four.py --check
python3 specialize_four.py --out /fresh/output
```

The generator verifies the checked generic input hash, preserves every
numbered helper formula and MP application, replaces each exact guard by
its shape constructor, adds the explicit four-schema interface, and checks
the resulting source hash. Small public-interface templates are in
`templates/four-prefix.txt` and `templates/four-suffix.txt`.
The output is byte identical to the independently checked source.
The source generator is untrusted; the proof kernel checks its output.

This extension is useful for exploring a source enumerator that constructs
a few fixed implication contexts instead of comparing two arbitrary
codes. Such a compiler would need a fresh scheduling and machine binding
proof. Building larger duplicated terms and enumerating extra parameters
may cost more states than the guard saves. No 215-state or 214-state TM
construction is asserted by this result.

The compressed proof retains the Source 149 / CD230 ancestry of the pinned
ProveIt proof at aa66d0a33f1f8237a348899eb8095b045a502832. The new result is
the exact four-schema sufficiency proof and all-code C222 adapter, built
on the separately documented 117-to-84 helper compression.
