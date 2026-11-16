# Literal M6 machine and revised source controller

The [archived binary table](../../../../../docs/pa194_radix_family_2026-11-13/machines/6/machine.tm)
has 194 working states and SHA-256
`725ce8474d7b83473488fc9466548ed2de3744d9a80183467894f9d719103ab2`.
The generator pins the dense table, reconstructed native table, label
map, trie sites and nodes, and resolved source instructions.

The [startup proof](PA194M6Startup.lean) transfers the complete 58,320-step
blank run from PA1944L. Lean checks that the two tables agree away from
controls 107 and 123, which the checked PA1944L startup avoids. The
[initializer](PA194M6Initializer.lean) lifts this run to arbitrary
arithmetic `IΣ₁` models and identifies its endpoint as the exact M6
configuration for source site 25.

The [controller theorem](PA194M6Controller.lean) relates literal machine
halting to reachability of site 10 in the [M6 source](README.md). It
uses the verified register operations and a finite premise covering all
3,795 sites. The [final literal theorem](PA194M6PhysicalFinal.lean)
applies the checked certificate for every site to discharge that
premise. The arithmetic calibration from the revised source to PA
consistency remains open.

From the repository root, pass the checked M6 source stage and the common
startup stage produced by
[`check-common-startup.sh`](../check-common-startup.sh).

```sh
variants=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants
bash "$variants/pa194m6/check-physical.sh" /path/to/m6-source /path/to/common-startup /path/to/fresh-m6-literal
bash "$variants/check-linear-coverage.sh" PA194M6 /path/to/fresh-m6-literal /path/to/fresh-m6-coverage
bash "$variants/check-controller-final.sh" PA194M6 /path/to/fresh-m6-literal /path/to/fresh-m6-coverage /path/to/fresh-m6-final
```
