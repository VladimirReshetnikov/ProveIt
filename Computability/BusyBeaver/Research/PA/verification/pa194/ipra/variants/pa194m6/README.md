# M6 source verification

The [archived radix-six candidate](../../../../../docs/pa194_radix_family_2026-11-13/machines/6/)
has 194 working states, with 3,795 resolved source instructions.
The source replay pins `instructions.json` by SHA-256
`03afe51960fe2345637a0e3ea25987a8544612124ad728874cbc45ef1de9126d`.

At site 123, the first revised multiplication loop consumes register 7
in units of one and adds six to register 1 for each unit before exiting
at site 131. The generated `PA194M6Constructor.firstMultiply` proves the
result for arbitrary register values in the arithmetic model, with a
positive model-valued clock.

The [source control proof](PA194M6Control.lean) checks that source site
10 halts at ordinal 3,796 and the malformed ordinal is 3,795. It proves
both ordinals absorbing at every model-valued source clock. The
constructor-site generator checks all 61 delivered constructor
occurrences and instantiates the common Cantor-pair constructor proof at
each entry and exit. The full arithmetic calibration of the radix-six
proof search to PA consistency remains open.

From the repository root, pass the checked primary native literal model
stage that provides `PA194ModelMPDrain.olean`.

```sh
radix=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194m5
bash "$radix/check.sh" "$PWD" /path/to/pa194-literal-model /path/to/fresh-m6-source 6
bash "$radix/check-cons.sh" /path/to/fresh-m6-source /path/to/fresh-m6-cons 6
bash "$radix/check-cons-sites.sh" "$PWD" /path/to/fresh-m6-cons /path/to/fresh-m6-sites 6
```
