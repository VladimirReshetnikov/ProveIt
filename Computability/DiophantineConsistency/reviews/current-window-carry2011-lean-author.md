# Author record: actual-port source-window carries

Result: author fresh compilation and focused checks PASS.
`controller_certificate` authored the specialization below. ROOT authored
the generic `NativeWindowCarry` theorem and assigned this concrete
composition. Independent review is a separate role.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| CurrentWindowCarry2011.lean | 94f9ec318d90b66200757bba8992eb6560e283dbdceeac877e48eee80ade3d06 |
| CurrentWindowCarry2011Checks.lean | 9965e414792135147823cf7e68d9cc2225a884f8030d18cee4cacb33be1cd080 |

The four ports are exactly `CurrentMasks2011.ports (CurrentKernel2011.K : Int)`:
beta, the literal displayed K, the low mask, and the native high mask plus
beta once. The complete mask interface is proved by the existing concrete
mask theorem and natural-number nonnegativity of K. K is not an arbitrary
parameter in this module.

`source_carries` starts with a strictly positive natural assignment of all
31 source coordinates satisfying all 22 source residuals. Its remaining
premises identify a Boolean word with the source gap, identify the source
q with `rho^n`, and identify a radix-bounded mask word with
`MF_native*J-1`. The cyclic length n is nonzero. These are explicit word
bindings, not tile, phase, refutation, or native-acceptance assumptions.

The proof discharges the folded-K congruence using `CurrentKernel2011.folded_word`
and discharges the full carry budget using its exact coefficient mass.
The generic source-window theorem then produces cyclic carries bounded
by57 and radix digits whose word is exactly the source F. It proves both
the local quotient recurrence and the local addition equation, and every
digit passes the corresponding mask test. The temporal term is the actual
binary rotation of the source gap word; no alignment is assumed.

The author read both complete final files and freshly compiled them
serially using `lake env lean -M6000 -j1 -o ...` against the final checked
kernel object. The 40-line main module exited0 with an empty log. The
32-line checks exited0, verified all four actual ports and positive K,
and exercised the source endpoint by extracting its exact F word and
local mask tests. Both axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.

| Final log | SHA-256 |
|---|---|
| /tmp/current-window-carry2011-final.log | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| /tmp/current-window-carry2011-checks-final.log | 3515ca8a08ed75bb1912c9db359c6be5c902cc658fcec5091f30a8c4b5da6f74 |

This is a concrete arithmetic source endpoint. It does not itself
reconstruct the word bindings from the polynomial, prove count/phase/tile
semantics, or establish equivalence to Con(ZFC).
