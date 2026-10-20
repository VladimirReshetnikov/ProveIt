# The remaining K/S-only commutation obligation

The [structural note](analysis.md) isolates the exact missing translated rho4
family on stable translated codes. It also proves an all-Heyting-algebra
obstruction: a native model cannot interpret membership solely through the
formula values of its numeric arguments. The literal gated bundle at
`(16,16,0)` is false in every such model, even when each numeric label has
its own distinct quantifier operation fixing top and bottom.

This excludes a countermodel design, not the K/S-only calculus. It supplies
neither a model of that calculus nor a proof of the missing commutation family.
The [reviewed mixed-row calibration](../README.md) avoids that obligation by
changing rho4. The two results have different scopes.

`review_upstream_reflection` authored the structural analysis. Root
independently checked the original calculation and strengthened it by removing
its unnecessary restriction on quantifier indexing. The [original note and
receipt](history-v1/) remain intact. Their suggested requirement to separate
R/E/Q label components was broader than the argument establishes; the current
note requires extra information only for membership. [review.json](review.json)
and [publication.json](publication.json) retain exact source bindings and the
correction. No solver, supplied program or proof assistant was executed.
