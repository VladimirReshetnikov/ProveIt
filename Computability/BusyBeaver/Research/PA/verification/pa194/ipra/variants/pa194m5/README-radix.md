# Radix constructor decoding

In every PRA model, `PA194RadixModel.encode` encodes two Cantor-paired
components and a radix digit. `decoded` recovers both components and the
digit when the digit is less than the radix. `constructorInj` rules out
equality between different tags or components. `reconstruct` gives the
inverse identity for every modeled number, including a number whose digit is
unused by the logical constructors.

For a radix of at least two, `decoderDescent` proves that both decoded
components of every positive input are strictly smaller than that input.
This is the bound for hereditary recoding of the numerical formulas and
their variable labels. It also applies at radix five before any restriction
to the four logical tags.

Supply a staged PA194 model replay that exposes
`PA194MachineProjections.olean`, such as the primary native literal stage.

```sh
dir=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194m5
bash "$dir/check-radix.sh" /path/to/checked-pa194-model /path/to/fresh-radix-output
```

`PA194RadixSplit` supplies unary primitive-recursive codes for the quotient
and remainder by each fixed positive divisor. The code parameter is the
largest digit, so parameter 4 implements division by five. The modeled
recurrence increments the remainder and carries into the quotient at that
digit. `modelQuotient` and `modelRemainder` identify the outputs in every
PRA model with an `IΣ₁) reduct. These functions can now be used in the
formula-and-label recoding history.

Pass the output of the safe M5 source checker to its replay script.

```sh
bash "$dir/check-radix-split.sh" /path/to/checked-safe-m5-source /path/to/fresh-radix-split-output
```
