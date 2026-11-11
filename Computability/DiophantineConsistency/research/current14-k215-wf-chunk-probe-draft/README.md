# K215 bounded well-formedness chunk probe

Source-only proposal to copy the original three finite tables into a private helper namespace and kernel-check the first 32 of 487 actual `nodeOkb` checks. The remaining 455 checks, root facts, full assembly, original-module equivalence and 490-stage continuation are separate. Original project sources and failed attempt are untouched. The helper imports only `RMEquiv` and `DagPerm`, both present in the authenticated fresh base. No Lean run yet.
