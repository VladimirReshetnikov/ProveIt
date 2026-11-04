# Concrete-support raw low identity draft

This uncompiled client applies the checked radix-and-indices identity to the concrete support using the separately checked support bound. It deliberately leaves the actual `lowNat` binding to a later stage so that this individual check isolates concrete-support specialization. The two input objects come from distinct captured provider unions; a runner must pin both and verify their complete selected closures and compatible companion bundles before using them together.

The [independent source review](../../reviews/trace74-concrete-low-raw-draft-independent/README.md) found no mathematical blocker and did not run Lean. Even successful compilation would provide only the raw low identity. The short defect's strict bound, high bound, final cover and model cast remain separate, as do graph and iPRA claims. The earlier timeout logs do not establish whether this narrowed specialization will be inexpensive.
