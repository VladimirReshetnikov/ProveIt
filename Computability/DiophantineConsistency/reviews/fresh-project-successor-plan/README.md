# Source-declared v2 to v3 successor survey

The [survey](v2-v3-declared-plan.json) compares the 1,210-module frozen AQ29
source graphs. It identifies one changed source, 86 modules in its reverse
project dependency closure, and 1,124 outside that closure. The source and
workspace hashes were audited at the observation point; no compiler dependency
verification or successor replay follows from this survey. The live v2 pair
must finish and pass before any parent objects can be considered for reuse.

The separately tested [conservative preparer](../../research/fresh-project-rebase/README.md)
requires authenticated parent-pair and coordinator-terminal evidence and
rechecks actual parent direct imports. Its output remains only a seed plan;
the affected modules must still be rebuilt and the equivalence checked.
