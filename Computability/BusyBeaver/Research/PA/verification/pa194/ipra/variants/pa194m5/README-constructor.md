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
