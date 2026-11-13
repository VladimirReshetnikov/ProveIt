# Independent review of the current14 low-mask bindings

This is a source and receipt review, not a fresh Lean run. The two retained
author04 observations for `LowMaskDisplay.lean` and `LowMaskInteger.lean`
report exit 0, empty stderr and the expected axiom reports without `sorryAx`
or warnings. Read-only [`audit.py`](audit.py) rechecks both observations,
their before/after guards, current direct input and output hashes, and the
pinned source and TeX files; its captured result is [`receipt.json`](receipt.json).
At review time the actual direct-import search order selected the guarded
objects. This does not authenticate the transitive source, object, package,
dynamic or search-path ancestry.

The first source decomposes `lowSupport` into exponents 0–950, 960–985 and
1004. Its finite sum is `G₉₅₁(r)+r⁹⁶⁰G₂₆(r)+r¹⁰⁰⁴`. The second source
shows the full support sum is at most `beta = radix²⁰¹¹-1`: the support is a
subset of the full range, radix is at least two, and the geometric-sum
identity bounds the sum. It obtains `lowPort + support = beta` in naturals,
then casts this equality to integers; consequently the three subtractions
are ordinary exact integer subtractions. The formula matches the maintained
TeX source's displayed μ recipe in the reviewer's source inspection.
`CurrentMasks2011.ports K 2` is definitionally `lowPort`; the current
`CurrentWindowCarry2011.ports` source delegates to that tuple with its fixed
kernel. This inspection does not establish that the historical endpoint's
objects and these source definitions share authenticated ancestry.

This is **not the first Lean binding of μ**. The pre-existing
`CurrentMasks2011.lowPort_printed_recipe` states an integer recipe, and the
separate [four-port assembly](../../research/current14-literal-port-assembly/README.md)
has `Current14LiteralPorts.all_ports`, whose `mu_eq` uses that theorem and
whose other components assemble beta, K and the once-shifted high mask.
Its README reports an earlier successful author check and matching retained
object/input hashes, on mixed captured providers without a separate process
receipt. The [historical mask peer review](../current-masks2011-lean-peer.md)
also describes an earlier checked recipe, but its `CurrentMasks2011` and
`CurrentMaskRecipes2011` source hashes differ from the present files. The
two new low-mask files are an independently formulated/replayed route to the
same structured μ identity; no coherent join to the iPRA endpoint is shown.

Neither the low-mask files nor this review parse TeX or PDF semantics, bind
all compressed coefficient files, or prove the final equation equivalence.
The [separate display audit](../../research/adaptive-direct-ordinate86/PRINTED-CONSTANTS.md)
describes external finite comparisons and their scope.

Reproduce the receipt checks while the recorded temporary providers exist:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/current14-lowmask-bindings-independent/audit.py
```

SHA-256: `audit.py`
`54307d47630d8e7f3f030063ea2291dc2af0135db9515ce60068f99500eadd8c`;
`receipt.json` `5550d1dd510a13d640cdad7c4c49a6c84f8325dd52892d69bcb780232f5bd0b7`.
