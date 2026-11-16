# PA194LC_AX11H

The [archived dense table](../../../../../docs/pa194_loop_continuation_research_2026-11-14/additional/PA194LC_AX11H/machine.tm)
has 194 working states and SHA-256
`5f10f071e7118ff33aba822e05bae0331b4c78508656c3e945c31b0c6788f9c5`.
Its resolved instruction file has the same SHA-256 as the one used in
the [AX11H proof](../pa194ax11h/README-final.md).

`PA194LCAX11HInitializer.startup_root` checks the 57,922-step literal blank
run and identifies its endpoint with the initial source configuration in
each covered arithmetic model. `PA194LCAX11HController.halt_iff_site10`
relates literal halting to site 10 of the shared source, given the finite
coverage certificate for all 3,671 source sites of this table.

From the repository root, pass the stage produced by
[`pa194ax11h/check-controller.sh`](../pa194ax11h/check-controller.sh).

```sh
variants=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants
bash "$variants/pa194lcax11h/check-physical.sh" /path/to/ax11h-controller /path/to/fresh-literal
bash "$variants/check-linear-coverage.sh" PA194LCAX11H /path/to/fresh-literal /path/to/fresh-coverage
```
