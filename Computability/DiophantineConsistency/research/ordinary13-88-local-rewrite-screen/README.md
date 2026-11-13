# Exploratory local rewrites of the 88/30 graph

No graph with fewer than 88 live binary operations was found in the bounded searches below. This is a search observation, not a global operation lower bound or a positive-zero equivalence theorem. It does not modify the 88/30 parent, run Lean, or bind a graph to a PDF.

`local.py` pins the reviewed free-J 88/30 graph and existing local-search engine. At each single target, it screens one-gate and two-gate replacements in the engine's enumerated forms in both a port-uniform and an authenticated-current-port pass, using three deterministic assignments modulo 1,000,000,007. A separate helper screens earlier-node aliases and sign reversals whose immediate uses are all squares, using the port-uniform samples only. Leaves are existing earlier wires and integer literals 0–4. A replacement is retained only when a live-gate recount is below 88. Both one/two-gate passes tested 88 targets, 874,412 first gates and 22,968 second-gate queries; neither had a zero target or nonconstant division sample, and neither had a strict survivor. The uniform-only alias/sign helper also found none, and its double-negation alias control was detected. A surviving modular match would still require exact verification; a rejection applies only to the tested exact-target family, not to changes that preserve only zeros.

`beam.py` separately imports only the pinned existing structural search's node, graph, local ring-rewrite and replacement functions. It searches up to ten rewrite depths with width 300, retaining graphs of at most 90 gates, using the fixed seed shown in the script. The rules include reassociation, signed three-term reassembly, distributivity and common-factor extraction; sharing is recounted across the whole DAG. Its common-factor positive control reduces three gates to two. The beam's best graph remained at 88 gates; beam pruning makes this an observation rather than exhaustive coverage. This run seeks exact polynomial equality, not arbitrary zero-equivalent reparameterizations.

The scripts were each run twice with matching output. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-88-local-rewrite-screen/local.py > /tmp/ordinary13-88-local.json
cmp /tmp/ordinary13-88-local.json research/ordinary13-88-local-rewrite-screen/local-result.json
python3 -I -S -B research/ordinary13-88-local-rewrite-screen/beam.py > /tmp/ordinary13-88-beam.txt
cmp /tmp/ordinary13-88-beam.txt research/ordinary13-88-local-rewrite-screen/beam-result.txt
```

This packet does not cover arbitrary integer leaves, arbitrary three-or-more-gate replacements, all coordinated rewrites, changes of witnesses or positivity arguments, or zero-equivalent changes of the residual system.

Independent external review is recorded in
`../../reviews/ordinary13-88-local-rewrite-screen-independent/`.
