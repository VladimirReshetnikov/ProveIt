# PA194 recursive translation with a fixed truth code

`PA194TruthCode.lean` defines the arity-one primitive-recursive constant 7.
In every candidate-PRA model it equals the numeric constructor `pair 2 0 + 1`.
Under the additional IΣ₁ assumption, `modelTruthInternal` identifies this
value with Foundation's internal `qqVerum` syntax code.

`PA194CanonicalRecursion.lean` uses that code, and the concrete membership
and equality codes of `PA194ConcreteRecursion.lean`, to eliminate the separate
truth-code parameter. For all candidate-PRA models it checks zero,
membership, equality, nonzero implication, and universal constructor
equations; the universal constructor uses the second decoded field as the
binder. The decoder and pair-projection certificates are still supplied as
hypotheses, with their existence established by `PRA_has_concreteComponents`.

The implication and binder-closing operations remain explicit, unverified
binary-code parameters. `PA194ZeroAlias.lean` proves the exceptional alias's
logical equivalence in PA using `0=0` as truth; connecting that result to
this `⊤` code and the represented proof compiler remains open. These equations do not
establish recursive syntax correctness, PA calibration, machine
internalization, or either consistency implication. In particular, the
identification with Foundation typed syntax is stated only under IΣ₁.
Rebuild the full chain with the pinned overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-canonical-recursion.sh
```
