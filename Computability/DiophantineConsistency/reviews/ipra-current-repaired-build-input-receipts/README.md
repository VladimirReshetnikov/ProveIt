Both input preparers exited 0, as observed through the tool sessions identified in
`receipt.json`. The adjacent logs reproduce their complete observed stdout;
they are transcriptions of the terminal responses, not logs produced by an
in-process recorder. The captured scripts, manifests and drift counts were
rehash-checked when this receipt was written.

The first packet completed successfully with the earlier replay driver and was
preserved under `ipra-current-repaired-build-before-drift-fix`. The later packet
uses the driver that records a disappearing workspace source as drift. Neither
preparation constitutes a Lean replay. The captured workspace observations do
not by themselves establish that sources stayed unchanged between observations.
The 848-project ancestor remains author-only, and external package-transitive and
dynamic ancestry are inherited.
