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
The [relative transfer](PA194LCAX11HRelativeNative.lean) then proves
that the two literal tables have equivalent nonhalting sentences in iPRA.
The [conditional endpoint](PA194LCAX11HConditionalFinal.lean) composes
this with the checked AX11H equivalence. Its sole premise is the
candidate's finite source coverage.

From the repository root, pass the stage produced by
[`pa194ax11h/check-controller.sh`](../pa194ax11h/check-controller.sh).

```sh
variants=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants
bash "$variants/pa194lcax11h/check-physical.sh" /path/to/ax11h-controller /path/to/fresh-literal
bash "$variants/check-linear-coverage.sh" PA194LCAX11H /path/to/fresh-literal /path/to/fresh-coverage
```

Use the checked AX11H final stage and a stage from the
[shared bounded transfer replay](../../../../shared/isigma1-machine/check-relative.sh)
to replay the conditional endpoint.

```sh
bash "$variants/pa194lcax11h/check-native.sh" /path/to/fresh-literal /path/to/ax11h-final /path/to/bounded-transfer /path/to/fresh-native
```

The [final endpoint](PA194LCAX11HFinal.lean) supplies the generated coverage
proof to the conditional theorem. Its theorem
`PA194LCAX11HFinal.consistency_iff_literal_nonhalt` states the equivalence
between PA consistency and literal blank-tape nonhalting in the standard iPRA
theory.

```sh
bash "$variants/pa194lcax11h/check-final.sh" /path/to/fresh-native /path/to/fresh-coverage /path/to/fresh-final
```
