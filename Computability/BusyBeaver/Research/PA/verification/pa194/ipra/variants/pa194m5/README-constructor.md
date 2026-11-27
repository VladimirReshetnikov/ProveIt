# Model proof of the M5 implication constructor

The M5 source at sites 102 through 129 implements the arithmetic constructor
whose exit is site 130. Its first eight rows decode a Cantor stack value. Three
rows restore the remaining stack. Ten rows compute the Cantor pair of the
popped value and the old top. The last seven rows multiply that pair by five.

`PA194ProgramCons.execute` verifies the same constructor at any certified
source ordinal and coefficient. If the input stack is `cantor left rest`
and the two scratch registers are zero, the output top is
`coefficient * cantor left oldTop`, the stack is `rest`, and the scratch
registers are zero. It preserves all other registers and the arbitrary
register-file suffix. The proof supplies a positive model-valued source
clock using the safe executable source dispatcher.

`PA194M5Cons.rows` checks the exact delivered source rows from the pinned
`PA194M5Program` list. `PA194M5Cons.firstCons` proves this updated store and
a positive clock for the first full M5 constructor. The literal physical
execution and the complete radix-five calibration remain separate proof
obligations.

Build the safe source stage using `check.sh`, then pass its output to the
constructor replay.

```sh
dir=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194m5
bash "$dir/check-cons.sh" /path/to/checked-safe-m5-source /path/to/fresh-cons-output
```

The delivered source binding identifies all 61 M5 constructor occurrences.
Its `source_binding.json` is pinned to SHA-256
`a75d3c991682ea4ee5a55243303d97764bc72ac71fb6e41a2aa2e4b0818f10d9`.
`PA194M5ConsSites.checked` verifies the complete 28-row source slice at each
specified ordinal. `PA194M5ConsSites.constructors` applies the exact
model-valued constructor theorem at any of the 61 sites.

After the constructor replay, check all of those source slices and their
execution theorem.

```sh
bash "$dir/check-cons-sites.sh" "$PWD" /path/to/checked-cons-output /path/to/fresh-sites-output
```

## Modus ponens prefix

[`PA194M5MPPrefix.throughConstructor`](PA194M5MPPrefix.lean) proves the
exact source execution from site 3614 to site 3682. It decodes the
argument, pushes the old top, copies the offset, and builds the
radix-five implication at the last of the 61 constructor sites. The
theorem gives the full resulting register file and a positive clock
in each covered model, with the two scratch registers 6 and 7 zero on
entry.

```sh
dir=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194m5
bash "$dir/check-mp-prefix.sh" /path/to/checked-m5-cons-sites /path/to/fresh-mp-prefix
```

## Modus ponens return to dispatch

The [comparison and cleanup](PA194M5MPGuard.lean) verify the branch
at site 3682 against arbitrary modeled comparison operands. The
[complete command](PA194M5MPCommand.lean) combines both outcomes
with the prefix and proves positive-time execution from site 3614 to
dispatch site 25. The [result identities](PA194M5MPFields.lean) give
the radix-five equality test and the resulting scheduler fields.
The command starts after the argument has been fetched into register
8. Connecting the command to the model scheduler requires the
preceding fetch and dispatch.

```sh
bash "$dir/check-mp-command.sh" /path/to/checked-mp-prefix /path/to/fresh-mp-command
```

The [scheduler-frame proof](mp-frame/README.md) adds the preceding
fetch and dispatch and compares the result to the coded radix-five step.
