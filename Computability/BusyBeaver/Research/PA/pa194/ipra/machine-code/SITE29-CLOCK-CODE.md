# Site-29 exact primitive-recursive clock

`PA194Site29DynamicClock.exactClock` replaces the site-29 physical segment's
existential running time by an explicit model-valued exact clock. It composes
the already checked dynamic path-29-to-30 step's primitive-recursive segment
costs, including the model-valued suffix count. Its staged replay passed in
`/tmp/pa194-site29-dynamic-clock-check.log`.

`PA194Site29ClockCode.clockCode : Code 13` compiles a term denoting that clock.
Its inputs are padding parameter `k`, suffix count, and the eleven logical
argument slots. `modelClock` proves that evaluating the code in any PRA model
gives the exact clock expression. The code/meaning theorem has passed a
fresh source rebuild against retained physical stages; the full auditing
wrapper `check-site29-clock-code.sh` passed with exit 0. Its log is
`/tmp/pa194-site29-clock-code-check.log`. The input and output physical
frames, clock expression, and suffix premise are in the two source files.

These are one-instruction semantic model results; they do not yet prove a
native iPRA sentence, model-length physical execution, or a consistency
implication. The source replay uses prebuilt machine and foundational stages;
it does not rebuild their entire transitive source closure.

The checker rebuilds these sources in a fresh output, in order:
`PA194Site29ReturnInterfaceDefs`, `PA194Site29StartInterface`,
`PA194Site29Complete`, `PA194Site29DynamicSelectedReturn`,
`PA194Site29DynamicSelectedAndSix`, `PA194Site29DynamicReturnFileToHeader`,
`PA194Site29DynamicReturnToRoot`, `PA194Site29DynamicReturnPath30`,
`PA194Site29DynamicOutput`, `PA194Site29DynamicComplete`,
`PA194Site29DynamicClock`, and `PA194Site29ClockCode`. Input source hashes
and retained direct object hashes are pinned; overlap and unchanged-input
audits are also performed. The checker rejects `sorryAx` in axiom reports.

Example replay from the repository root, with a previously nonexistent output:

```sh
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-site29-clock-code.sh "$PWD" \
  /dev/shm/pa194-site27-coherent/build \
  /dev/shm/pa194-site28-work/build-carry-seven \
  /dev/shm/pa194-site28-work/build-one-spare-file-roundtrip \
  /dev/shm/pa194-site28-work/build-carry-roundtrip \
  /dev/shm/pa194-site28-work/build-site29-selected-return \
  /dev/shm/pa194-site28-work/build-finish-return \
  /dev/shm/pa194-site28-work/build-site29-to-increment \
  /dev/shm/pa194-site28-work/build-complete \
  /dev/shm/pa194-site28-work/build-site29-return-to-root \
  /dev/shm/pa194-site28-work/build-site29-path30-identities \
  /tmp/current14-standard-fresh-build-20261104/lib \
  /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-site28-work/build-site29-clock-code-replay-2
```
