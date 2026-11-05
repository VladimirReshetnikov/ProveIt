# 80-to-81 quotient graph binding

For any commutative ring `R`, `liftRing` replaces coordinate 9 of an 81
valuation `v` by `v 9 + v 7`, leaving all other coordinates unchanged. The
six Lean theorems `first`, `main`, `strong`, `auxiliary`, `transport`, and
`output` prove equality of the corresponding 80 and 81 expression evaluations
under that substitution. In particular, the checked equality is for the
actual generated Lean graphs, not merely modular samples. The theorem does
not assert that every 80 valuation has a positive 81 preimage or establish a
zero-existence equivalence or iPRA endpoint.

On 2026-11-04 the following Lean invocation exited 0; each of the six printed
axiom reports contained `[propext]` and no `sorryAx` or warnings. A subsequent
bounded [guarded replay](lean-replay.json) exited 0 with the same six exact
reports and a byte-identical object. It recorded [the complete output](lean-replay.log),
the exact command, and before/after hashes for the source, Lean executable,
and both direct graph objects. The [runner](check_lean.py) refuses to overwrite
its output and its receipt; a rerun needs a fresh output location in a copy.

```sh
LEAN_PATH=/tmp/p64-independent-captured-replay/lib:/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 180 /home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -M4000 -j1 -DElab.async=false \
  --root=Computability/DiophantineConsistency/research/fourteen-p64-qcube80-binding-draft \
  Computability/DiophantineConsistency/research/fourteen-p64-qcube80-binding-draft/P64QCube80Binding.lean \
  -o /tmp/P64QCube80Binding.olean
```

| Artifact | SHA-256 |
| --- | --- |
| `P64QCube80Binding.lean` | `53462826fc52467434d87676079262487fb31a24104ca0857562791ca281e452` |
| `/tmp/P64QCube80Binding.olean` | `09e60861c431b6780f179f1200e3897f3d958215eac0e076bd8f6251cf235179` |
| `/tmp/P64QCube80.olean` | `e8829517e10e4c3d2423594dd884b86466834d7714038660030d16861c8abd68` |
| `/tmp/P64QCube81.olean` | `f2b88d807ac99ebfa8a73b25ed354a302b93a35f53eda9816b3c842502b7a64f` |
| `check_lean.py` | `435d87f356fc55332a43ec89d99b533855ee5b444f719d68fec7b554a03b4818` |
| `lean-replay.json` | `c9b28764e7842b8c5342023acc41a3885b9fc4141a6bbdbcd79fa35ed417ae39` |
| `lean-replay.log` | `217a257b8a87ae15b76802a957bacca7f0a87e76a6793fe8df31c3fbc53473d6` |
| Lean binary | `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550` |

The table reports artifact hashes from the observed checks. Full transitive source/object, package,
dynamic-library and search-path ancestry of the captured providers was not
independently audited in this check.
