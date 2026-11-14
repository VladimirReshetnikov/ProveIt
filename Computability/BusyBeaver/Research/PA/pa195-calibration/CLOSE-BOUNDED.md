# PA194 bounded-depth term closing

`PA194CloseBounded.lean` constructs an explicit primitive-recursive code
`closeDepth first second h` for each **externally chosen standard** depth bound
`h`. Each level dispatches the encoded bound-variable and free-variable tags
and function terms of arity 0, 1, or 2, using the recursively supplied code for
children. These arities cover the function arities of the arithmetic language;
the code's behavior on other tags or arities is not a generic closing theorem.

The external inductive `Shape M` describes finite term shapes with arbitrary
model-valued symbols and variable indices. `modelCloseDepth` proves, in every
candidate-PRA model and for every external shape of height at most `h`, that
the code computes the numerical closed shape. The closing label, indices,
depth parameter, and function symbols can be nonstandard model elements.
The proof requires candidate-PRA certificates for two pairing projections,
whose existential availability is established in `PA194StackCode`.

This is a metatheoretic family of codes with an externally finite shape and
height bound. It is **not** one primitive-recursive closing code for arbitrary
model-valued syntax or nonstandard term depth, and it does not yet connect the
numerical result to a generic Foundation `closeLabel` rewriting theorem. It
also does not prove a full formula translator or a consistency implication.
The preceding one-step constructor and named-Foundation identification
results are in [TERM-DISPATCH.md](TERM-DISPATCH.md).

Run from the repository root with the audited overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-close-bounded.sh
```
