# Shared implication core for the Rocq K215 lane

This contribution replaces the pinned Rocq dominated-implication certificate
replay by the same representation-independent 58-step proof already used by
the Lean lane, and adds five detachments exposing the K/S/Peirce basis.

Repository snapshot: `2ca3a5c16f0876d2cab842056353c03a1ed2f5f0`.

## Result and scope

The final eight-module closure compiles with Coq 8.18.0 / OCaml 4.14.1.
Recursive `coqchk K215F.Audit` exits successfully. All eleven printed
assumption reports are closed under the global context: six generic exports,
two Nat-code exports, the unchanged `thmDom_iff`, and two typed interface
clients. The earlier baseline certificate and unchanged client were compiled
and recursively rechecked separately.

This is a focused compatibility check, not a fresh build of the 237-source
production Rocq 9.1 closure or the full ZFC endpoint. The only adaptation in
the three unchanged K215 client modules and the baseline certificate is the
library namespace spelling `From Stdlib Require` to `From Coq Require`.
The two arithmetic-code dependencies are byte-identical to their pinned
repository originals. `provenance.json` gives their exact sources and hashes.

## What becomes simpler

| Checked source | Lines | Bytes |
|---|---:|---:|
| Production `DomRho8.v` at the pinned commit | 1,169 | 22,673 |
| New generic core, including K/S/Peirce | 311 | 15,310 |
| Nat-code compatibility adapter | 54 | 2,307 |
| Combined replacement | 365 | 17,617 |

The replacement has 68.8% fewer source lines and 22.3% fewer bytes, while
providing more public theorems. These figures compare checked proof sources;
the untrusted renderer, derivation file and archival baseline are separate
artifacts. The compact production certificate contains 735 instructions and
272 symbolic term entries. It is not meaningful to identify those instructions
one-for-one with the 58 condensed-detachment steps: substitutions are explicit
certificate operations in one representation and type instantiations in the
other. The new common derivation has 58 MP nodes and five further MP uses for
exchange/S; the retained `lift_right` wrapper applies MP once more.

`Language` requires only a carrier, a binary implication operation, and a
reflexive relation closed under embedding into either operand. The proof does
not require transitivity, antisymmetry, a truth constant, an injective code
constructor, a formula decoder, natural-number arithmetic, or normalization.
The Nat adapter supplies `below := Nat.le`, with the two growth laws derived
from the existing Cantor-pairing bounds. Its existing `dtruth` field remains
for compatibility but is not used in `rho8_all_of_restricted`.

The generic core also applies to an unrestricted implication calculus by
taking `below := fun _ _ => True`. This is the same instantiation used by the
companion Lean refactor to replace the older independent Lukasiewicz proof.

## Files and reproduction

`src/K215F/DominatedImplication.v` is generated; `src/K215F/DomRho8.v` is the
small hand-written Nat adapter. `src/K215F/ThmDom.v` and the other inherited
client files are unchanged apart from the namespace spelling. `Audit.v`
checks the exact old public theorem types. The original sources and the
current 58-step plan are retained under `upstream/`.

Run in a directory with Coq 8.18 or a compatible installation:

```sh
python3 reproduce.py --out /tmp/k215-rocq-core
```

The driver verifies pinned inputs, requires exact regeneration, compiles
baseline and final candidate in distinct trees, checks the expected closed
assumption reports, and runs recursive `coqchk`. It uses no admission, added
axiom, unsafe flag or trusted native computation. Logs, source/object hashes
and local timings are written below the output directory. The distributed
`evidence/` contains the observations from this run; timings are not a stable
whole-project benchmark.

The generator can be installed next to the existing derivation renderer:

```sh
python3 render_core.py \
  --renderer /path/to/rho8cd/generate_domrho8_cd.py \
  --derivation /path/to/rho8cd/derivation_core.txt \
  --output /path/to/coq/215/DominatedImplication.v
```

## Production integration

1. Add the generic module to the K215 compile order immediately before
   `DomRho8`; replace `DomRho8` by the adapter. Use the production standard
   library prefix if desired; the generic module has no imports.
2. Update `regenerate215.py` to call this renderer for the generic module
   and copy the small adapter instead of invoking the old compact-certificate
   renderer. The current generator branch is the `name == "DomRho8"` case.
3. Refresh the normal regeneration receipt and manifest through the existing
   production workflow, then rebuild the affected closure under Rocq 9.1 and
   rerun the two sparse/dense endpoint assumption reports and recursive
   `coqchk`. The focused check here does not replace that gate.

`proof-source-only.patch` applies the two proof-source changes to the pinned
repository, using the production `Stdlib` prefix in the adapter. It passed
`git apply --check`; it does not perform steps 2 or 3 above.

The standalone package deliberately leaves the live production generators,
receipts and endpoint verification status untouched. It is a reviewable
proposal with a checked immediate client, ready for that integration.

## Attribution

The 58-step proof plan and its search/unification machinery are inherited
from ProveIt. This contribution adds its abstract Rocq rendering, the Nat
adapter and explicit K/S/Peirce sharing interface, with reproducible focused
verification. It makes no novelty claim for Lukasiewicz's axiom, K/S/Peirce,
condensed detachment, Cantor pairing, or the existing K215 machine.
`LICENSE.ProveIt` and the inherited upstream scope notice are retained.
