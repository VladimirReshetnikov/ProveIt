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
PRA model with an `IΣ₁` reduct. These functions can now be used in the
formula-and-label recoding history.

Pass the output of the safe M5 source checker to its replay script.

```sh
bash "$dir/check-radix-split.sh" /path/to/checked-safe-m5-source /path/to/fresh-radix-split-output
```

`PA194RadixRecoding` gives a primitive-recursive history for hereditary
recoding of the paired numerical constructors. It preserves every
available digit, reads the already computed recodings of the two decoded
components, and maps an unavailable digit to zero. The components include
numerical variable labels. `recodeConstructor` checks that action uniformly,
including the zero constructor. `recodeDigit` fixes the truth and
falsehood indices 0 and 1.

`radixFiveRoundTrip` proves that recoding from radix four to five and back
returns every original model value. The generic `injective` theorem applies
whenever the target radix contains all source digits and the source radix
is at least two. These statements use the explicit primitive-recursive
function codes in arbitrary PRA models with an `IΣ₁` reduct.

The source replay takes the two decoder stages above.

```sh
bash "$dir/check-radix-recoding.sh" /path/to/radix-model /path/to/radix-split /path/to/fresh-recoding-output
```

`PA194RadixRestrictedImplication` instantiates the archived finite
`rho8All` proof template in the modeled natural order for any radix at
least one. Each implication code is at least each of its two operands.
Those two inequalities discharge the order conditions within the template.
The theorem supplies the unrestricted row from the restricted row and
modus ponens, so recoding a restricted leaf can use this template at its
recoded operands.

```sh
bash "$dir/check-radix-rho8.sh" /path/to/radix-model /path/to/fresh-rho8-output
```

The [constructor](PA194M5RecodeConstructors.lean) and
[head](PA194M5RecodeHeads.lean) identities show that the recoder carries
the primary logical constructors, emitted heads, guarded separation,
and the diagonal formula to their radix-five values. Injectivity
preserves and reflects the equality tests on variable labels.

[`PA194M5ProofTransport.proofTransport`](PA194M5ProofTransport.lean)
uses the primary proof-history induction in arbitrary modeled natural
numbers. Given a Σ₁-definable predicate closed under the radix-five
rules listed in `FiveClosure`, it sends any primary target theorem
to that predicate at its recoded index. Its refutation specialization
sends primary provability of 1 to the predicate at 1. The remaining
connection is to instantiate the predicate with the M5 search and
prove its closure and reverse soundness.

```sh
bash "$dir/check-radix-transport.sh" /path/to/recoding-output /path/to/rho8-output /path/to/fresh-transport-output
```
