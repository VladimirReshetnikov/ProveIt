# Post-dependency-cut fixed source snapshot

Workspace and frozen-tree graph audits agree on 798 project modules, declared imports, source hashes, order, direct external objects and compiler/configuration anchors. Compared with the previous 848-source BaseCertificate graph, this graph removes 51 modules, adds `ParsonsPositiveSyntax`, and has 42 retained source changes. Exact lists and hashes are in the audited states and source-delta manifest. The 75-module witness-transfer comparison and 111-module 86-operation suffix each have topologically resolved declared imports against this graph, but require separate builds.

This is build input, not a proof result. Rebase on a passed 848 BaseCertificate parent. Reused-object original environments are reconstructed from surviving recorded providers; external package-transitive ancestry and dynamic imports remain inherited. Later workspace edits are not covered.
