# PA194GS

The [archived binary table](../../../../../docs/PA194GS_research_2026-11-15/machine/machine.tm)
has 194 working states and SHA-256
`64ac4ba569b770688a39a1545d5536ad631d15dbb756a0584a8956a83943b3a8`.
The generator also pins its native table, label map, trie sites, and
resolved instruction list. The resolved instructions match the
[proved AX11H source](../pa194ax11h/README-final.md).

The [literal controller proof](PA194GSController.lean) identifies the
57,922-step blank run with the entry frame for that source. It uses
checked native and dense row agreement and the literal register boxes.
The [shared AX11H controller](../pa194ax11h/PA194AX11HSharedController.lean)
then relates halting to reaching source site 10. Its finite premise
covers all 3,671 sites, and the [GS checker](PA194GSChecks.lean) checks
each site's resolved instruction and physical branches.

From the repository root, pass the AX11H controller stage produced by
[`check-controller.sh`](../pa194ax11h/check-controller.sh).

```sh
variants=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants
bash "$variants/pa194ax11h/check-shared-controller.sh" /path/to/ax11h-controller /path/to/shared-controller
bash "$variants/pa194gs/check-physical.sh" /path/to/shared-controller /path/to/gs-literal
bash "$variants/check-linear-coverage.sh" PA194GS /path/to/gs-literal /path/to/gs-coverage
```
