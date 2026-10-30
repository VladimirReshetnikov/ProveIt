# Full-source driver: first audit-only attempt

This graph-resolution attempt failed before any module compilation because the default Lake path did not contain the direct external object `Foundation.FirstOrder.SetTheory.Basic.Axioms`. The exact terminal state and then-current driver are retained. A subsequent driver must explicitly select and hash the inherited Foundation provider. This result is not a proof build.
