# Complete structural decoder coverage

`SiteCoverage.lean` proves that a Boolean check at every actual leaf transfers
to every successful register-program decoder walk with its exact consumed
path. The consumed path includes implicit zero bits when the supplied program
counter is shorter than the traversal. A second theorem derives existence of a
leaf walk for every counter, because `allSites` rejects `.none`.

The complete-tree proof composes both children at each internal node. A Python
list of paths is not a coverage premise. The generator may choose a cut
frontier for performance, but an omitted branch cannot satisfy the final
`allSites_join` composition against the actual tree.

The generic module passed pinned Lean 4.32.0 in 0.48 seconds. Seven axiom
reports and three callers passed in 0.26 seconds, using only `propext` and
`Quot.sound`. The callers include the empty program counter's implicit zero
branch. Reproducible source, compiler and audit evidence is in
`results/site-coverage-verification.json`.

`generate_sites_perm252.py` separately emits a complete cut of the literal
`ActualTree254.tree`: 233 chunks, 6,460 leaves, 8,391 zero/positive guard cases,
and depth 34. These counts and source generation are not kernel passes for the
actual site checks. The generated `SitesPerm252.lean` must separately check each
closed chunk and the final complete-tree composition. Even that result needs
the dispatch invariant and runtime composition before yielding a blank-tape
machine endpoint; standard-ZFC calibration remains a separate obligation.
