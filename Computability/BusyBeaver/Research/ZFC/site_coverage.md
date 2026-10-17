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

`generate_sites_perm252.py` emits a complete cut of the literal
`ActualTree254.tree`: 233 chunks, 6,459 internal nodes, 6,460 leaves, 8,391
zero/positive guard cases, and depth 34. All eight persisted guard batches and
the final complete-tree composition have now passed pinned Lean 4.32.0. Every
check expression and the final cut composition are unchanged from the original
monolithic source. The default generator's `--check` mode reproduces all nine
source files exactly.

The eight batch processes took 2,995.40 seconds in total; the final join took
13.01 seconds. Their largest resident-memory measurement was 6,093,156 KiB
(5.81 GiB). Each batch saved its own checked object before the next process
started, within its 900-second and 8-GiB limits. These are observed resource
measurements, not a bound on another host. Complete source identities,
commands, individual timings, logs and object hashes are in
`results/sites-permutation252-verification.json`.

The final audit passed 23 axiom reports and seven caller controls in 0.65
seconds. `all_sites`, `actual_walk_checked`, and `actual_walk_exists` use
`propext` and `Quot.sound`. The closed endpoint callers additionally use
`Classical.choice` through the existing program/theory proofs. No custom axiom
or coverage premise occurs in those callers. They compose the literal
82,552-step bootstrap, complete runtime simulation, and actual register-program
endpoint to prove blank-machine halting equivalent to `Code254.C254 Code254.F`,
native CP/all-Form-GIC/IR refutation, and actual `ZFax_s` refutation. Controls
also reject a path of length 41 and register index nine.

The original monolithic 233-chunk attempt was externally terminated by SIGTERM
without a Lean diagnostic or output object. It was incomplete and never
passed. Its exact source and interruption evidence remain recorded separately;
the eight successful modules preserve its check expressions rather than
restarting that monolithic process.

The separately checked dispatch and runtime modules are documented in
`results/permutation252-runtime-integration-verification.json`. The closed
coverage removes their previous all-sites premise for this exact machine.
The standard-ZFC Choice consistency comparison and arithmetic internalization
remain separate obligations; this result asserts neither unconditional
nonhalting nor machine minimality.
