# Edge-owned graph grammar v1

Top level: `schema` is `proveit.graph-grammar.v1`; `nodes` is a nonempty array; optional `root` selects a node (default: last).

## Leaf

```json
{"kind":"leaf","vertices":3,"edges":[[0,1,1]],
 "terminals":[0],"isolated_vertices":[2]}
```

Vertex names are integers 0 through vertices-1. Edge triples are [u,v,positive integral capacity]. Repetitions are parallel edges; u=v is a loop. Terminals are ordered and distinct. Every nontrivial leaf vertex must appear in an edge, a terminal list, or the explicit private `isolated_vertices` list. The latter is optional when empty and cannot overlap vertices already named by edges or terminals. One isolated singleton leaf may omit the inventory.

## Binary join

```json
{"kind":"join","left":0,"right":0,
 "left_map":[0],"right_map":[0],"terminals":[0]}
```

Child indices precede the current node. Each map has one label per ordered child terminal. Together, the labels are exactly 0,...,q-1 for some q. Equal labels identify vertices, including self-identification within one child. Parent terminals are an ordered distinct subset of those labels. Every use is a fresh copy of child edges and private vertices. All edges survive with their capacities.

## Unary map

```json
{"kind":"map","child":0,"mapping":[0],"terminals":[]}
```

The same quotient-label rules apply to the one child. Removing a class from the terminal list forgets it but does not delete its graph vertex or edges.

## Responses and certificates

A response key is (terminal_color_mask, exact_edge_flags). Terminal bit i colors terminal i. Flag bit 0 records at least one color-zero monochromatic edge; bit 1 records a color-one edge. Missing keys mean no realization of cost at most k. Costs of stored keys are minima.

A complete certificate contains each table as [mask,flags,cost,witness] records, graph metadata, the threshold, and a SHA-256 source digest. Leaf witnesses are coloring bit masks; other witnesses name child keys. A soundness-only witness DAG retains reachable (rule,key) pairs. An edge occurrence address contains the sequence of child choices from the root, then the leaf rule and edge index. It does not yet name an edge in a native triangulation.

The metadata uses hexadecimal strings for potentially huge expanded vertex, edge, and hidden-component counts; it retains the current terminal component partition and terminal degrees capped at four. Its private-cubic flag applies to vertices no longer exposed as terminals. At a terminal-free root this is a whole-graph cubic check, not an embedding check.
