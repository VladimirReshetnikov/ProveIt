# Standard-iPRA client for the 40-variable quartic

`draft/IPRAStandardQM40.lean` adapts the existing direct-square standard-theory
client to `IPRAQM40Native.literal_equivalence`. It states both the native
refutation-negation equivalence and the Gödel–Gentzen-translated selected
Foundation consistency sentence. It has compiled in a [guarded author-side
extension](author-rebuild/README.md); its opening uncompiled-source comment
is historical. The result does not establish a PDF-byte binding.

The completed extension rebuilt the four standard-theory modules on the
native provider. A direct transplant from the historical standard overlay was
not justified by the [provider survey](provider-preflight/README.md).
The successful run remains single-author and inherits the native provider's
project, package, transitive and dynamic ancestry; a paired replay is open.
