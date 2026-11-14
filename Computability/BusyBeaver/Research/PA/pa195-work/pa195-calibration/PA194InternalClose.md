# Model-internal term closing

`PA194InternalClose.lean` compares `PA194TermRecursion.closeCode` with a
new instance of Foundation's internal `Language.TermRec.Construction` for
closing a free label. On a bound variable with index below the insertion depth,
the construction leaves the index unchanged; it shifts any other bound index
by one. It replaces the selected free variable with the bound variable at the
insertion depth, leaves other free variables unchanged, and traverses function
arguments. This is a new use of Foundation's general term-recursion interface;
Foundation's existing `termSubst` is a different operation, which substitutes
bound variables and leaves free variables unchanged.

The theorem `agree` says the two term-closing results are equal for **every**
model-internal well-formed arithmetic semiterm of the given depth. The term
code, depth, and selected label may all be nonstandard model elements. It
assumes a nonempty model of the candidate `PRA` language, equality interpreted
as equality, an `IΣ₁` arithmetic reduct, and `PRA` proofs certifying the two
pairing projection codes. `canonical_agree` fixes certified projections once
and for all and removes the last two premises. `close_well_formed` proves the
Foundation construction's result is well formed at depth plus one. The typed
corollary `typed_canonical_agree` has a standard external depth because
Foundation's typed `Semiterm` is indexed by `Nat`; its internal term code and
label may still be nonstandard.

The proof uses the Σ₁ graph of each finite candidate-PRA function code and
Foundation's Σ₁ induction on internal semiterms. Lean reports only
`propext`, `Classical.choice`, and `Quot.sound` as axioms for the exported
results; in particular, none depends on `sorryAx`. This proves neither formula
traversal nor the PA194 machine/refutation equivalence, and by itself is not
an object-theory derivation of either direction of that equivalence.

Run `check-internal-close.sh` with `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` set to the audited project and Foundation object
directories. It compiles dependencies and the comparison into a fresh temporary
overlay and checks the displayed axioms for `sorryAx`.

An independent fresh Linux replay of `check-internal-close.sh` also passed with
those overlays, including the dependency rebuild and the axiom check.
