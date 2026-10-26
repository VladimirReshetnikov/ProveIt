# Current decoded window: independent composition review

Date: 2026-10-26 UTC. Reviewer: `controller_certificate`. Root authored the
new composition and checks; the reviewer changed neither source. Result:
PASS for the exact endpoint and scope below.

Authorship boundary: I authored the imported `CurrentCellLabels2011`,
`DoubledClause2011`, `CurrentPolynomialWindow2011`, and
`CurrentWindowCarry2011` dependencies. This is an independent review of
root's new composition, not an independent review of my own dependencies
or a claim of independent authorship throughout the imported chain.

Frozen reviewed sources, read in full:

| File under `Lean/DiophantineConsistency/` | SHA256 |
| --- | --- |
| `CurrentDecodedWindow2011.lean` (79 lines) | `fd52d069a146d13287cd7da987cc54117e19282efabba6c30c9b4a4f2a48b217` |
| `CurrentDecodedWindow2011Checks.lean` (27 lines) | `5b94a5a4f16dc82cdfe38b2fc831185082be8ae96a69217768d8bd5be347b053` |

I also read the complete current `CurrentOneHot2011` and
`CurrentPolynomialWindow2011`, checked the full `Facts` fields and actual
four-port definition, and inspected the invoked physical-equivalence,
early-padding and fractional-phase interfaces. Their relevant bindings are:

* `CurrentOneHot2011`: `45e9cd33fb50e4fc16f524948fc2f68a4dfbd334dd64e7fda114b3c55946842c`;
* `CurrentCellLabels2011`: `88698cd0d678d788c169b22915594b9ce37dd5d5c19c3d0069b190e0575f740d`;
* `CurrentPolynomialWindow2011`: `db64a1e9130d09d606f3262781be9a4c0d70db1a9cdb7482cd74ecc0ddf0b730`;
* `CurrentWindowCarry2011`: `94f9ec318d90b66200757bba8992eb6560e283dbdceeac877e48eee80ade3d06`;
* `WangTiles942Permutation`: `3351336105f22baf653dcefb3bd83273924dd539353eebf5f1232da855045cef`.

`facts_decode_cell` applies the actual one-hot and phase results to the
same `v`, `N`, source vector, Boolean word, carries and normalized digits.
The shift is exactly the original core rank's natural value minus
`47*(N*2011)`. The decoder receives that shift, literal support, bounded
carries, local convolution equations and actual mask tests directly from
the same `Facts`. It does not switch to independently chosen witnesses or
assume zero incoming carry, decoded labels, occupation, or whole-field
alignment. Its outgoing clause carry is a conclusion.

The dependency order is noncircular at this composition boundary. The
literal count result discharges its middle-phase tests using actual early
padding; fractional phase zero then uses the origin and the physical count.
Only after those results does this new module invoke full label decoding.

`facts_start_south` uses `Facts.origin`, the proved physical position of
abstract tile0, and the actual `start_zero` tuple. The known selector value
one at the origin rules out the empty decoder branch and selects Start;
the South projection is therefore510. No occupied-cell premise or assumed
Start label bits are supplied.

`facts_terminal_south` uses the actual inverse of the proved physical
permutation at physical941. Applying the inverse law identifies that
selector with the given `c(b+941)=1`, and the full decoder supplies its
South complement. The conclusion retains the fixed expression
`511-(tile (physicalEquiv.symm 941)).south`. It neither evaluates a cached
terminal value nor excludes511, so it is compatible with the real511
self-loop relevant to the later cycle argument.

`polynomial_zero_decoded_window` obtains one positive window length and
one complete `Facts` witness from the actual fourteen-coordinate polynomial
at all four fixed2011 ports. It preserves that witness while adding decoded
labels and clause reset at every aligned cell. Its only premises are
positivity of the fourteen original integer coordinates and evaluation of
that actual polynomial to zero. The focused endpoint explicitly names
`Carrier65.polynomial CurrentWindowCarry2011.ports`, checking the alias.

Independent sequential replays, Lean `v4.32.0`:

```sh
lake env lean -M6000 -j1 -o /tmp/current-decoded-window2011-peer.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentDecodedWindow2011.lean
lake env lean -M6000 -j1 -o /tmp/current-decoded-window2011-peer-checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentDecodedWindow2011Checks.lean
```

Both exited zero. The main replay log is empty, SHA256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The checks log SHA256 is
`6f1624d2d47c7bf6b5650de09352ed33d47d3a47570585c0cee77ea9d6db8fc0`.
All four axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. The main source was independently elaborated to a temporary
object; the checks import the root-built object for the same pinned source.
This is not a fresh replay of the entire imported dependency closure.

No correction is requested. Empty cells remain permitted. Whole-field
alignment, occupation propagation, matching adjacent colors, native
machine semantics, the reverse existence direction, and the final
consistency equivalence are not conclusions of this packet.
