# Proposed standard-iPRA client for the 40-variable quartic

`draft/IPRAStandardQM40.lean` adapts the existing direct-square standard-theory
client to `IPRAQM40Native.literal_equivalence`. It states both the native
refutation-negation equivalence and the Gödel–Gentzen-translated selected
Foundation consistency sentence. **This source has not been compiled**; it
does not independently establish either endpoint, nor a PDF-byte binding.

The native QM40 replay and a coherent provider containing the standard-theory
objects are separate prerequisites. A candidate historical source of the
latter is `/tmp/ipra-standard-current14-author-trial/lib`; its available
objects do not by themselves authenticate a combined provider. Before using
it, check module resolution and matching shared imports against the actual
QM40 native provider and retain all inherited ancestry qualifications.
