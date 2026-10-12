# Component-Gauge Cut Atlases for Compressed Unknot Hierarchies

Research continuation prepared for Vladimir Reshetnikov's **ProveIt** project, 12 October 2026.

**Main result:** exact marked small-cut queries on supplied, edge-owned graph grammars are polynomial-time at every fixed threshold, even when intermediate pieces have arbitrarily many disconnected terminal-bearing components. The construction answers the factorized-response question in ProveIt report 91. It does **not** establish an unrestricted quasi-polynomial unknot recognizer.

The article is `article/component_gauge_atlases.pdf`; its standalone source is `article/component_gauge_atlases.tex`. It includes complete proofs, a quantitative complexity analysis, attribution, a source audit, measured gains and regressions, and further research questions. Repository inspection and the report-91 compatibility check are pinned to:

```text
d5c9a97fac1803258ea675297e4a7b22b78dd79b
```

## Mathematical contribution

An atlas row stores an exact cut cost, terminal colors relative to one root per connected component, component-relative monochromatic-edge flags, and the actual aggregate flag of components with no remaining terminal. Visible component root colors remain independent symbolic bits. Joins impose XOR equations; a forgotten component's root bit is eliminated through a four-state OR computation. Tags stay attached to their component variables until they are transported or eliminated.

For a piece with `r` terminals, the number of rows of exact cost `d` is at most

```text
4 (d + 1) max(1, 8r)^d.
```

For two child interfaces of width at most `W`, the number of row pairs satisfying the shared budget `a+b <= k` is at most

```text
16 binomial(k + 4, 4) max(1, 8W)^k.
```

This removes the earlier exponential component factor, without increasing the interface exponent to `2k`. The total deterministic complexity has the form

```text
poly(s, L, W, B, k) exp(O(k log(L + W + 2))).
```

Here `s` is the number of rules, `L` the listed leaf size, `W` the largest interface, and `B` the relevant integer bit lengths. Positive integral capacities, explicit leaf inventories, fresh-copy use of children, and terminal-only vertex identifications are essential premises. Arbitrarily large numeric thresholds are not charged merely by their binary length.

The delivery also proves and implements an **equivariant coloring DAG**. One recipe represents a valid coloring for every assignment of visible root bits; witness export does not enumerate these assignments. At most `k` cut-edge occurrence addresses, and one monochromatic-edge address per present color, can be extracted without expanding the represented graph.

Precompiled linear gluing plans and minimum-only descriptor dominance are proved as further optimizations, but are **not implemented or timed** in this version.

## Reproduction

Python 3.10 or later; standard library only. The recorded runs used Python 3.13.5. From this directory:

```sh
PYTHONPATH=src python -m unittest discover -s tests -v
PYTHONPATH=src python experiments/replay_delivery.py
PYTHONPATH=src python experiments/audit.py
PYTHONPATH=src python experiments/benchmark.py
sh article/build.sh
```

The benchmark is separate from unit testing and takes longer. It overwrites its data outputs; the article's embedded tables record the delivered run and do not silently change when a benchmark is rerun. PDF rebuilding requires `pdflatex` and the packages declared in the source. A `Makefile` exposes the same commands.

A complete graph query with independent replay:

```sh
PYTHONPATH=src python src/query.py examples/prism.json --check \
  --certificate /tmp/prism-gauge-certificate.json
```

A graph-schema compatibility query on the actual pinned report-91 fixture:

```sh
PYTHONPATH=src python integration/query_report91.py \
  examples/report91_triangular_prism.json
```

A work limit aborts inconclusively rather than proving absence. A complete checker exception also means that no certified verdict is available; it must never be interpreted as a negative graph or knot answer.

## Minimal programmatic use

```python
import json
from pathlib import Path
from gauge_cuts import compile_grammar, extract_cut_addresses
from checker import verify_packet, verify_coloring_recipe
from coloring import build_recipe, mark_address

grammar = json.loads(Path("examples/prism.json").read_text())
packet = compile_grammar(grammar)
verified = verify_packet(packet, expected_grammar=grammar)
print(verified["query"])

if verified["query"]["status"] == "MARKED_CUT":
    ri = next(i for i, row in enumerate(packet["atlases"][-1]["rows"])
              if row[3] == 3)
    recipe = build_recipe(packet, ri)
    verify_coloring_recipe(recipe, expected_grammar=grammar)
    cut_edges = extract_cut_addresses(packet, ri)
    mark_edges = [mark_address(recipe, color) for color in (0, 1)]
    print(cut_edges, mark_edges)
```

A complete packet checks all exact costs and all rows, including absence of rows. A coloring recipe checks **existence only**, not minimum cost or absence of another coloring. Always supply the expected source grammar when binding a proof to a caller-owned graph.

## Input and output contracts

The native delivery grammar has exactly `k` and `nodes`; the last node is the root. A leaf explicitly lists `vertices = [0, ..., n-1]`, weighted `edges = [[u,v,capacity], ...]`, and ordered `terminals`. A unary `map` or binary `join` has `children`, one terminal quotient map per child in `maps`, and ordered surviving quotient labels in `keep`. Quotient labels are dense and explicit. The examples contain both operation forms.

Every child reference creates a **fresh copy** of its edges and private vertices. Only listed terminals can be identified. An edge is never deleted, aliased, or reweighted by a join. A private vertex cannot be promoted later. The graph can have loops, parallel edges, isolated vertices, and an empty interface.

The complete certificate schema is `component-gauge-cut-atlas-v1`; the positive symbolic schema is `component-gauge-coloring-v1`. An atlas row is

```text
[exact_cost, terminal_parity_integer, component_tag_list, hidden_mask]
```

Masks `1`, `2`, and `3` mean that a monochromatic edge of color zero, color one, or both colors is present; `0` means neither. Component tags use colors relative to that component's root. Hidden masks use actual colors. A symbolic color `[i,b]` means `X_i XOR b`; `[-1,b]` is constant `b`.

The command-line program returns abstract graph statuses only: `MARKED_CUT`, `NO_MARKED_CUT`, `OPEN_INTERFACE`, or an error/inconclusive status. It never returns `UNKNOT`.

## Executed evidence

The delivery passes **48 unit-test methods**. The deterministic audit includes all **1,100 labeled simple graphs through five vertices**, **33,867 terminal-subset projections**, **1,000 weighted multigraph leaves**, **1,000 random grammars**, **3,105 complete certificate replays**, and **2,102 symbolic coloring replays**. Detailed counts and their exact meaning are in `data/validation.json` and Section 10 of the article.

Binary stress cases include `2^512` hidden edge components, nested powers of disconnected channels, 1,024 free terminal components, and a programmatic 16,385-bit edge capacity. The latter is not advertised as a default JSON round trip: Python's decimal-integer parser/encoder limit is distinct from its arbitrary-precision integer arithmetic.

In the supplied 18-component interface benchmark, the atlas has peak two rows versus 262,144 explicit states; query medians are about 0.775 ms and 2,232 ms respectively. The final graph has easier alternative parses, so this is a representation-specific comparison, not a lower bound against every graph algorithm. On the two-channel depth-64 power, the atlas is slower: 196.6 ms versus 153.1 ms. Raw paired measurements, alternating order, and A/A controls are retained.

The real report-91 prism fixture translates and independently replays with 53 stored rows, six final vertices, nine edges, cubic metadata, and minimum both-mark cut cost three. This is graph compatibility, not native triangulation integration. Neither the native recognizer nor a knot corpus was run.

## Integration boundary

Place this intact delivery in a new report directory, choosing its number at intake. Do not overwrite production defaults. See `integration/INTEGRATION.md`, `CLAIMS.md`, and `SOURCE_AUDIT.json`.

For the topological threshold-three interpretation, the caller must additionally authenticate a unit-edge cubic pattern on the sphere bounding a certified 3-ball, account for vertex-free circles, and bind graph occurrences to source charts. Graph cut addresses are not themselves embedded violating discs. A faithful geometric exporter, disc transport, and global hierarchy/restart accounting remain separate requirements.

Lackenby's inspected 2021 handout states the announced scale as `2^{O((log n)^3)}`. The article distinguishes that global target from its own local `n^{O(log n)}` regime when `k = O(log n)`.
