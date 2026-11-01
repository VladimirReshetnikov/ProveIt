# Native-image and MF-refactor fixed source snapshot

Workspace and frozen-tree graph audits agree on 793 project modules, source hashes, declared imports, order, direct external objects and compiler/configuration anchors. Relative to the 798 MF-cleanup parent graph, five MF modules leave the closure and four retained sources change; the new 75 comparison and 111 adaptive source orders were checked for source hashes and unresolved imports. Exact module and source-delta lists are recorded in the graph states and manifest.

This is fixed build input, not a proof result. Rebase on the passed 798 MF-cleanup parent. Original reused-object transitive environments are reconstructed from surviving recorded providers, and package-transitive ancestry and dynamic imports remain inherited. Two native image modules also changed in the separate native extension and must be rebuilt there.
