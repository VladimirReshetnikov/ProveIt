# Small quadratic graphs for annotated syntax constructors

`AnnotatedSyntaxGraphs` supplies an exact direct graph for the actual wire
constructor

```text
forkCode(a,b) = Nat.pair(a+1,b)+1.
```

It uses three auxiliary naturals: a branch bit `t`, an order slack `s`, and
the maximum pairing component `m`. Its four integer residuals are

```text
t(t−1)
m − ((1−t)b + t(a+1))
b + ts − (a+1) − (1−t)(s+1)
out − 1 − m² − (a+1) − tb.
```

Each residual is quadratic. `forkCertificate_sound` and
`forkCertificate_complete` prove that their simultaneous vanishing over
natural values is equivalent to the exact constructor equation. The proof
also derives `out>0`; no positive-output premise is assumed. The exposed
`system` can be instantiated into an existing shared register context using
the checked `System.instantiate` API.

The supplied `forkGraph` is the sum of squares of these rows, has total degree
at most four, has exactly three natural witnesses, and uses 54 binary tree
operations. `forkGraph_saves_five` compares actual graph data: the previously
supplied `AnnotatedCodeGraphs.forkConstructor` uses eight witnesses.

## Formula data without large quoted numerals

`atomGraph n` computes `n*n+1` using the original atom label as its only
numeric coefficient. `treeGraph` builds supplied graph data by structural
recursion on an actual finite tree, and `formulaGraph` applies it to the
existing `quoteForm` syntax. This construction never inserts the enormous
quoted tree/formula value as a literal coefficient.

The universal checked metadata formula is

```text
(treeGraph t).witnessCount = 5 * forkCount t.
```

A fork contributes its three local auxiliaries and two composed argument
outputs. The theorem permits closed counts to be proved by traversing small
syntax metadata alone, without constructing a closed formula-graph expression
or calculating a large formula-code numeral. It gives the following exact
counts for the seven fixed unsealed ZFC bodies used by the new dispatcher:

| Body | Natural witnesses |
| --- | ---: |
| Extensionality | 105 |
| Regularity | 105 |
| Power set | 135 |
| Pairing | 130 |
| Union | 135 |
| Infinity | 235 |
| Choice | 330 |

`fixedBodies_graph_counts` proves the complete table from the universal
metadata theorem. These are formula-construction graphs, before their
bound/sealing certificates and axiom dispatch.

The local fork graph is quartic. The recursively composed formula graphs
have the witness counts above; this checkpoint does not give them a quartic
degree bound. Attaching the exposed quadratic rows in a shared register
context is the interface for preserving degree four throughout a complete
constructor system. A generic graph composition may increase polynomial
degree and require further flattening.

## Validation and scope

The dedicated check file verifies both pairing branches, zero-output
rejection, an invalid branch bit, an invalid order slack, the zero-witness
atom graph, the exact local degree/count theorems, and all seven closed
count-only formulas. The source supplies computational decidability of the
named local certificate predicate. Both module and checks compile with no
errors or warnings; six runtime controls return true and twenty-one printed
axiom audits use only the standard three axioms, or fewer.

The frozen complete PR checker remains unchanged. This checkpoint does not
construct its full compiled graph, assert a whole-checker quartic variable
count, or change its proved external refutation language. Interpreting these
local polynomial certificates over internal omega still requires the explicit
model-level arithmetic correctness being developed separately.
