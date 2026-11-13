# Exact ordinary carrier indices for the free-J graph

`FreeJExactOrdinary.exact_ordinary_indices` works in an arbitrary model of
`IΣ₁` under the same conditional graph assumptions as its audited parent:
the actual 95-row free-J literal has an internal zero at twelve positive
model coordinates; the natural ports have β > 0, MC < β and MF < 2β when
interpreted in the model. The compact44 port interpretation and checker
calibration remain separate.

Writing `q = 1 + v₀β`, `a = v₅v₆ + v₆`, and
`c = v₈ + v₆(v₈ + v₉)`, and writing `R` for the precise model expression in
the theorem, it constructs positive first and main witnesses and main and
first Pell indices π and j with

```
13 ≤ j < π,       π = R,       2j = R + 1,
c = ycoord π a,
2 * ycoord j (2 * (v₅ * v₆² - 1) + 1) = v₈ + v₉.
```

The theorem also retains the corresponding `xcoord` equations. It derives
the required auxiliary signed residues from the actual graph and ordinary
strong and auxiliary norms, and uses the existing model `half_index` lemma.
It does not assume `Δ ∣ i`. Here π indexes the main carrier `c`. The earlier
ordinary-rank theorem's *different* index `m` indexes `f` and is only known to
be divisible by π; this theorem does not claim `m = R`.

This is a conditional model-level result using classical Lean metatheory, not
an object-level iPRA proof, a fixed-port zero characterization, or an
end-to-end equivalence. The indices and witnesses are proof objects and do not
add variables to the literal equation. Further carrier recovery and the
internal proof-existence bridge remain open.

## Evidence

The first exploratory attempt [source](observations/attempt01.lean) exited 1;
its [terminal log](observations/attempt01.log) records the evaluation bridge,
commutativity and association errors, and its `sorryAx` report is therefore
not proof evidence. The corrected author-only exploratory session 92297 exited
0 with the standard three metatheory axioms and no warnings.

The [paired replay](replay.py) pins the independently audited ordinary-rank
parent, both matched seed objects and inherited object chains, then compiles
this source separately over fresh author and peer overlays and checks its
direct imports. It does not rebuild the inherited chains. The graph parent's
manifest-at-read qualification and the Foundation outer-wrapper and package
transitive/dynamic ancestry limitations remain. The monitor samples resources;
it is not a continuous or whole-process-tree hard quota.

Actual outer session 82674 [exited 0](evidence/terminal.txt), printing
receipt SHA-256 `fec23d0d6fdc8b66041bf67b41f10a80e8dc3b9d48bd0b7138cfb6bf19374c6c`.
The [receipt](evidence/receipt.json) records both compiler and direct-import
checks exiting 0, matching objects, and the three standard axioms. The
[author](evidence/author.log) and [peer](evidence/peer.log) logs contain no
warnings or `sorryAx`. A subsequent [independent artifact audit](../../../reviews/ordinary12-freej-exact-ordinary-independent-audit/README.md)
passed for this suffix.
When the pinned temporary parents remain available and the Lean slot is free,
the paired replay is:

```
python3 -I -S replay.py --output /tmp/ipra-freej-exact-ordinary-new
```
