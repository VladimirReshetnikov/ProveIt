# Independent review: natural-80 combined slim source overlay

The [overlay packet](../../research/ordinary14-natural80-combined-slim-overlay/README.md)
accurately describes its bounded source composition. The original receipt and
the independent checker below both reproduce. This is a source-byte and
simple-header review, **not** Lean parsing, elaboration, dependency
resolution, provider compatibility, axiom closure, or an iPRA theorem.

The independent checker pins both inventories and the overlay checker,
reads and hashes all 184 original and inert snapshot files, and verifies
there are exactly 184 regular non-symlink `.lean.src` files. Of these, 171
match their prior natural-81 overlay snapshots, two use exactly the separately
pinned keyword-name alternatives, and eleven are the natural-80 additions
copied byte-for-byte from their pinned originals. The keyword changes are
exactly eight and seven code-token replacements, preserving the one English
comment. The review separately checks that both predecessor-order snapshots
and all six listed root74 slim-refactor snapshots remain byte-identical to
their earlier alternatives. Neither kind of edit has been checked by Lean.

The checker reparses the snapshots' initial simple import lines, verifies
each bare import precedes its consumer in the listed order, and traverses
backwards from `Natural80Endpoint` to confirm all 184 snapshots are
reachable. It hashes all 40 directly named qualified sources and checks their
identity against the pinned natural-80 inventory. Exactly
`C44Short15Facts` disappears relative to that original-header direct set,
and the three qualified additions relative to the natural-81 combined
source inventory match the overlay README. These are lexical observations;
they are not a resolved dependency cut.

The review shares the earlier pinned source inventories and does not
independently prove that their historical providers are authentic. Its parser
is intentionally limited to the observed initial simple import syntax. It does
not follow qualified sources' transitive imports, identify Lean's actual search
path or companions, exclude object collisions outside these source files,
reserve a Lean slot, or check package/toolchain/runtime ancestry. It does not
materialize the inert snapshots, run the source tactics, execute axiom reports,
or bind the symbolic equation to physical bytes or the PDF.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-natural80-combined-slim-overlay-independent/check.py | cmp - reviews/ordinary14-natural80-combined-slim-overlay-independent/result.json
```
