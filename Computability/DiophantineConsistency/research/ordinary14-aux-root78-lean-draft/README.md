# Source-only Lean graph for the direct-auxiliary 78/60 equation

`P78AuxRoot.lean` is generated literal `Expr (Fin 14)` source, **not an elaborated or compiled theorem**. The generator pins the separately reviewed 78-row candidate and emits the proposed `output_shape`; `--check` reproduces exact source bytes without invoking Lean. Slot 8 is the positive first Pell root (the graph names it `r`), slot 11 is the direct positive auxiliary root y, and slots 12 and 13 are gamma-prime and h. The four fixed leaves are beta, K0, MC and MF. Parser/elaborator, reduction/resource behavior, source/object/Init provider closure, a graph count theorem and external file association are untested.

The reviewed 78↔79 positive-zero argument is external standard-integer mathematics for beta>0. Its model proof requires more than this graph: a literal 79↔78 graph evaluation and slot-11 witness client; proofs from the candidate's own first/main/strong residuals of `1<Q` and `1<z²`; and the separately drafted conditional model witness map. `../ordinary14-aux-ring-norm-extraction-draft/` proposes a factor-level route from explicit ring residual equations to natural norms, but is uncompiled and still requires this graph's actual five-square zero extraction, field evaluations, positive natural parameters and signed Q/z bindings. The earlier `../ordinary14-aux-root-model-draft/` map assumes those two strict inequalities explicitly. All natural/ring coercions and changed-coordinate dependencies must be proved, not inferred from the external JSON delta.

The 79↔84 first-root and positive-valuation clients, 84↔85 modified-carrier proof, remaining parent model clients, compact44 cast/provider compatibility and iPRA endpoint also remain separately uncompiled/open. This packet does not read or identify PDF, JSON or gzip bytes inside Lean and does not prove a graph count, degree, consistency theorem or minimum.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-aux-root78-lean-draft/make_graph.py --check
```

Before any future Lean run, independently review all proposed sources and exact direct/transitive object/Init routes, check the established disk/resource guard and obtain the exclusive Lean allocation.

Independent source review is recorded in
`../../reviews/ordinary14-aux-root78-lean-draft-independent/`.
