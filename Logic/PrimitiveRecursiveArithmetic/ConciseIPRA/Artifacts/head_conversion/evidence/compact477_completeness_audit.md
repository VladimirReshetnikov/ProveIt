# Independent audit of the 477-byte canonical-completeness claim

Reviewed `research/checker_agent/proof477.tex`,
`research/checker_agent/compact477.py`, and the exact 478-byte control at
`output/ipra_head_conversion_2026-11-12/reference/incumbent_bytes478.py`.
Also inspected the named canonical emitter in the repository's
`Artifacts/guarded_source/implementation/source_dispatch/tests/global_producer.py`.

## Result and scope

The new completeness argument is supported **under its stated canonical,
guarded, closed-public-goal contract and the inherited completeness of
canonical compilation for the old scalar calculus**. I found no failure
caused by the new even-depth eager image checks. This is not a claim that
every arbitrary raw certificate accepted by the old checker is accepted
by the new checker, nor an independent mechanization of the inherited
scalar-calculus/iPRA translations.

The original wording "closed numerical source and seed" was too strong.
Those fields can contain negative rigid coordinates for eigenparameters
already allocated by the surrounding proof. The corrected text in
`proof477.tex` now states the needed condition precisely: numerical terms
well scoped at the current call floor, with no exposed image slot.

## Why the extra checks preserve canonical certificates

1. A genuine well-scoped numerical term inspected at numerical depth 3
   reaches only protected scalars. Successor adds 4 to depth, iteration
   adds 2, and the canonical encoding protects every locally bound
   coordinate. Already allocated rigid coordinates lie in `[k,0)`.
   Accordingly this inspection terminates without ever needing the
   omitted-image sentinel, and returns the same raw term in both
   programs. A later, smaller floor still protects all old parameters.

2. In a canonical formula or formula template, unary D and ternary Q
   preserve even formula-depth parity. Binary equality enters terms at
   odd depth, and numerical constructors preserve odd parity. Thus every
   unprotected meaningful numerical occurrence uses the odd branch.
   Multiplication by one and the old short-circuit operation have
   identical results there. Actual images are the well-scoped numerical
   terms from item 1. Canonical goal labels, meaningful hypotheses, and
   actual elimination endpoints are consequently identical.

3. The dispatcher eagerly computes the two proposed endpoint fillings
   even for arithmetic and introduction records, where the fourth field
   is numerical rather than a formula template. Viewing such a numerical
   tree at formula depth can reach even unprotected scalars. The new
   operation then checks the source or seed, and that check succeeds by
   item 1. Outputs of these unused endpoint calls can change from scalar
   zero to the empty list. They cannot trigger elimination: the
   administrative major is `[]`, whereas both reconstructed source-major
   shapes (`[s,u]` and `[t,t,t]`) are nonempty. For actual equality or Q
   elimination the template is a formula template, so item 2 instead
   gives literal agreement of the endpoint calls.

4. An auxiliary resource obtained by tripling a nonunary major can have
   surplus arity and ignored annotations. It is opened at the newly
   allocated integer parameter. At every newly eager image check this
   integer is protected at numerical depth 3 by the updated floor.
   Multiplication by zero therefore returns integer zero, not an empty
   list. The generated resource remains literally identical to the old
   generated resource, including ignored annotations. A unary D major
   yields the ordinary canonical Q resource and is already covered by
   item 2.

5. The one administrative discrepancy is intentional: the old neutral
   initial resource and administrative major are scalar zero; both are
   `[]` in the new certificate. Opening the empty list succeeds directly.
   Both spellings are falsy in the remaining dispatch tests. Canonical
   formulas and generated nonneutral resources are unchanged. Induction
   over the compiled trace therefore preserves the public goal and
   acceptance.

No optional metric search or broader regression testing was performed
for this audit. The conclusion follows from the invariant and branch
analysis above, rather than from the finite fixture counts.
