# Compact direct Lean derivation of dominated rho8

The [generated proof](../../../../../../../Lean/BusyBeaver/ZFC/DomRho8.lean) is reduced from 689,857 to 135,417 bytes (80.4%).
It retains 674 of the original 3,728 proof nodes and 994 of the 5,160 input terms.
The [generator](../../../../generate_domrho8_lean.py) reuses exact substitution instances of earlier theorem schemas,
then removes unused proof and term dependencies. This reduces the actual checked proof;
it does not relocate the old declarations into another module.

The optimizer and [original certificate](../../../../lean217/dominated_rho8_full_certificate.json) are untrusted proof producers.
Each retained step is an ordinary Lean theorem: truth, a dominated rho8 instance,
modus ponens, or substitution into an earlier theorem valid for every valuation.
The existing explicit conversion lemmas handle the native `wim 0 0 = 0` alias.
The public `DomImp`, `le_l`, `le_r`, `sub`, and `rho8_all` statements are unchanged.
No axiom, native evaluator, or semantic assumption is added.

The final generated source followed by [five typed API clients](API.lean) passed in
8.681 seconds with no warnings. Both axiom reports contain only `propext` and
`Quot.sound`: [actual log](actual/compiler.log), [invocation record](actual/result.json),
[exact checked source](actual/FinalWithAudit.lean). This local check is distinct from
the final endpoint dependency-closure validation performed by the parent build.
The [independent peer](peer-review.json) read the optimizer, emitter, exact public
contracts, generator reproduction and compiler record without rerunning either tool.

Generator reproduction from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/lean-rho8/reproduce.py --out /tmp/domrho8-reproduction
```

This uses a disposable input copy and checks exact output equality; it does not invoke
Lean. The [recorded portable reproduction](reproduction/portable-result.json) passed.
For a fresh endpoint kernel check, use the serialized [Lean build driver](../../lean/README.md).
It uses the shared machine-wide compiler lock and preserves all compilation attempts.

The [generator delta](generator.diff), [previous generator](history/generate_domrho8_lean.before.py),
[compressed previous proof](history/DomRho8.before.lean.gz), and
[experiment summary](history/experiments.json) preserve the reduction's provenance.
Earlier full generic-interpreter attempts exceeded their bounded kernel checks; none
of those failed objects is used. Their complete scratch sources remain outside this
accepted packet. The successful direct proof deliberately uses opaque earlier theorem
results instead of reducing one large interpreter execution. See [summary.json](summary.json)
for exact hashes, sizes and scope.
