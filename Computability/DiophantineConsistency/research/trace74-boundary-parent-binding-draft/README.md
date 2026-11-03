# Unchecked boundary binding drafts

These four files are source proposals only. They have not been elaborated or kernel-checked; no Lean process was launched for them. They are intended to turn the conditional same-witness reverse data into a positive 74 zero while allowing the old trace75 third coordinate to be zero:

- `Trace74BoundaryParent.lean` adapts the checked natural trace shift and all-ring mask coordinate identity. It assumes positivity for every old coordinate except index 2 and separately assumes a positive representative of the new mask. It proposes to shift coordinate 4, then replace index 2 with that mask; the inverse ring-coordinate map recovers the old, possibly zero, index 2.
- `Trace74BoundaryParts.lean` combines the proposed parent map with the checked `old_output_zero` algebra for one tuple of Pell/carrier witnesses.
- `Trace74BoundaryNatural.lean` adapts the checked natural-register binding. It retains the old-coordinate mask inequality `F+alpha<q`, which holds at the boundary `F=1, alpha=0, q=2`; it does not assume the desired new-coordinate guard `F+C<q`.
- `Trace74BoundaryGraph.lean` adapts the checked unscaled reverse construction and is intended to consume `Trace75UnscaledReverseData.reverse_data` with the same source witnesses and produce a positive 74 zero. It uses the positive old mask separately from the possibly zero old index 2.

The next task is to review the draft and its selected provider closure, then author-check staged modules under a resource guard. The exact finite R=31 seed is in `../trace74-boundary-31-seed/`. Specializing the conditional graph theorem to that seed would still need a checked finite arithmetic certificate (the Pell ordinate `k` alone is about 14,417 bits). All current evidence is for arbitrary ports; it does not establish the fixed BFS tuple, and neither these drafts nor the partial seed is a formally checked 74 zero, model equivalence, or iPRA endpoint.

Independent source-level review is recorded at `reviews/trace74-boundary-parent-binding-draft-independent/`. It found no definite mathematical mismatch in the same-witness mapping; Lean elaboration, provider closure and concrete seed specialization remain unchecked.
