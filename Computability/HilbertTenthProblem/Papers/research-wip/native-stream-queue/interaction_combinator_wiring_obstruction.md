# A finite wiring obstruction for interaction combinators

Two closed nets of four interaction combinators have the same cell counts,
the same labelled underlying graph, the same counts of every unordered
port-type pair, and the same initially enabled interaction. Nevertheless,
one reaches a net with no agents and two cyclic wires, while the other stops
with two agents. This rules out an exact reachability representation whose
entire dependence on the input net factors through that summary. It also
rules out an exact one-step update function on that summary.

This is a concrete obstruction to one possible compression of graph memory.
It is not a lower bound for topology-aware Diophantine representations, and
it does not improve a universal-polynomial operation bound. Both example
nets normalize. The distinguishing event is **agent-free reachability**, not
normalization.

## The universal substrate and the simulated fragment

Yves Lafont's *Interaction Combinators*, Information and Computation 137
(1997), 69–101, gives three agent symbols, `gamma`, `delta`, and `epsilon`,
and six rules, one for each unordered pair of symbols. Figure 2 on journal
page 81 gives the complete table; Theorem 1 on page 82 states the translation
of any interaction system into these combinators. Sources are the
[author's paper](https://www.i2m.univ-amu.fr/perso/yves.lafont/pub/combinators.ps)
and an [inspected PDF copy of the same paper](https://chorasimilarity.wordpress.com/wp-content/uploads/2024/01/ic-lafont-1.pdf).

The definitions on journal page 71 (PDF page 3) number the principal port
`0` and the ordered auxiliary ports `1,2`, and allow cyclic wires with no
ports. The numbered annihilation picture on journal page 82 (PDF page 14)
joins equally numbered auxiliary ports for `delta–delta`. This matters:
the two binary symbols do not use the same annihilation convention.
The [checker](interaction_combinator_wiring_obstruction.py) simulates only
this actual `delta–delta` rule. The all-`delta` fragment is terminating and
is not claimed universal; it supplies a counterexample within the larger
universal system. The source URLs, inspected file hashes and page locations
are pinned in the [receipt](interaction_combinator_wiring_obstruction.json).

## Literal nets and exact terminal predicates

A net in this packet consists of a finite sorted list of distinct natural
cell identifiers, a perfect matching of their ports, and a natural number
of agent-free cyclic wires. Every cell is a `delta`. Port `(c,p)` has integer
identifier `3*c+p`; `p=0` is principal and `p=1,2` are auxiliary. There are
no free ports. Self-wires between different ports of the same cell are
allowed. Each port occurs exactly once in the matching.

An active pair is a wire joining two principal ports. For this fragment:

- `is_normal(N)` means that `N` has no active pair.
- `is_agent_free(N)` means that `N` has no cells. Cyclic wires are allowed.
- `is_exact_target(N)` means that `N` has no cells and exactly two cyclic
  wires. In the closed domain there are then no port-incident wires.

These predicates are distinct. In particular, the exact target is not the
completely empty net: its two cyclic components are preserved.

Use cells `A=0`, `B=1`, `C=2`, `D=3`. Both inputs have zero cyclic wires.
Their complete wire lists are:

| Wire | Net A | Net B |
|---|---|---|
| AB | A0—B0 | A0—B0 |
| AC | A1—C1 | A1—C1 |
| AD | A2—D0 | A2—D0 |
| BC | B2—C0 | B2—C2 |
| BD | B1—D1 | B1—D1 |
| CD | C2—D2 | C0—D2 |

Equivalently, in the exact wire order used by the checker:

```text
A = cells [0,1,2,3], loops 0,
    wires [[0,3],[1,7],[2,9],[4,10],[5,6],[8,11]]
B = cells [0,1,2,3], loops 0,
    wires [[0,3],[1,7],[2,9],[4,10],[5,8],[6,11]]
```

Both have the same labelled underlying graph `K4`, not merely isomorphic
graphs. Their complete unordered port-type histogram, ordered as
`(00,01,02,11,12,22)`, is `(1,0,2,2,0,1)`. Their unique active pair is `AB`.
They also agree on cell identifiers, agent counts `(0,4,0)` for
`(gamma,delta,epsilon)`, free-port count zero and cyclic-wire count zero.
The function `summary` retains exactly these data, including the labelled
underlying edge multiset and initial active-pair identities.

## Port gluing, including cycles

Annihilating cells `u,v` removes their principal–principal wire and joins
`u1` to `v1` and `u2` to `v2`. The endpoints here denote the former auxiliary
ports before suppression. Construct a temporary multigraph from all other
old wires and those two new joins. Former auxiliary ports have degree two;
surviving ports have degree one. Every component is therefore either a path
with two surviving endpoints or a cycle with no surviving endpoint.

Replace each path by the wire joining its two surviving endpoints, and
replace each cycle by one agent-free cyclic wire. Preserve pre-existing
cyclic wires. Parallel temporary edges must be retained: an old wire that
coincides with a new join forms a two-edge cycle, not a disappearing edge.
The checker implements exactly this component construction and validates
that the output remains a perfect matching.

For net A, annihilating `AB` leaves

```text
cells [C,D], wires [C0—D0, C1—D1, C2—D2], loops 0.
```

Now `CD` is active. Its annihilation yields two two-edge cycles, one for
each auxiliary label, and no cells. Thus A reaches the exact target in two
steps.

For net B, annihilating the same `AB` leaves

```text
cells [C,D], wires [C0—D2, C1—D1, C2—D0], loops 0.
```

There is no principal–principal wire. This is a normal form with two cells.
The only first step was `AB`, so no alternative reduction sequence from B
can reach any agent-free net. No other combinator rule can intervene because
the nets contain only `delta` and the only applicable rule preserves that
restriction. Both paths terminate; each step removes two cells.

## What the counterexample proves

Let `S` be the displayed summary. We have `S(A)=S(B)`, but exactly one of
`A,B` reaches an agent-free net, and exactly one reaches the fixed two-cycle
target. Hence no predicate of `S(N)` alone can decide either event for all
these nets. In particular, no polynomial certificate of the form

\[
N\text{ reaches the target}\quad\Longleftrightarrow\quad
\exists \mathbf z\in\mathbb N^k\;P(S(N),\mathbf z)=0
\]

can satisfy this equivalence on every input in the packet's domain. The
reason is simply that its right side is identical for A and B. Allowing
more quantified coordinates, higher degree, or a different witness domain
does not distinguish identical parameter tuples. This statement applies
only when *all* dependence on the initial net factors through `S`.

Moreover, the summaries of the two unique successors differ: A has active
pair `CD`, whereas B has none. Therefore there is no function taking only
`S(N)` to the correct summary after the unique enabled step on these
inputs. An abstraction may still overapproximate transitions, and a
topology-aware exact encoding may retain additional incidence data.

## Arithmetic-complexity relevance and outstanding costs

The fixed three-symbol, six-rule controller is attractive. The example
shows why eliminating the association between graph edges and their ports
is not justified even after preserving substantial global statistics.
An exact compiler must retain enough information to validate the chosen
principal pair, read its incident wires, perform the specified joins,
preserve untouched wires, and account for cyclic components.

In the full rule table a mixed `gamma–delta` interaction replaces two
cells by four. For an input with `C0` cells, a trace of `T` sequential
interactions has at most `C0+2T` live cells and can use at most `C0+4T`
allocated cell identifiers if every new cell receives a fresh identifier.
These are storage bounds from the rule shapes, not Diophantine circuit
counts. An unrolled finite-horizon graph certificate still grows with the
horizon. A fixed-size universal equation would need a separately justified
history or memory compression and all of its arithmetic charges.

This packet also does not supply an ordinary-integer input loader for one
fixed universal net. The source's computable translation of interaction
systems does not itself pay for such a loader. Neither that interface nor
the topology-aware memory representation is treated as free here.

## Replay and finite search receipt

Run from the repository root:

```sh
/tmp/diophantine-research-venv/bin/python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/interaction_combinator_wiring_obstruction.py
```

The default mode recomputes the evidence and compares it with the saved
JSON without writing it. `--write` regenerates the author receipt. Public
replay entrypoints include `examples`, `check_net`, `summary`, `active_pairs`,
`annihilate`, `normalize`, the three terminal predicates, `audit_pair`, and
`exhaustive_search`. Validated net inputs use exact Python integers;
Booleans, floats, malformed matchings and noncanonical wire lists are
rejected.

The saved search enumerates all `11!! = 10,395` perfect matchings of the
twelve labelled ports on four cells. Exactly `1,296` give labelled graph
`K4`; this also equals `(3!)^4`, since each cell assigns its three ports
to its three distinct neighbours. The search checks all reduction orders
for every input and finds one terminal net per input, including cyclic
wire counts. It checks `5,670` initially enabled pair choices in total.
The K4 inputs have 15 port-histogram classes, four of which contain both
agent-free and non-agent-free normal forms. These histogram classes are a
search aid; the displayed witness pair additionally matches the stronger
full summary and unique active-pair identity.

The receipt contains the complete witness pair and both traces, hashes of
all enumerated input/normal-form records and the K4 subcollection, source
provenance, and the result of 102 malformed-call rejections. Separate edge
cases verify preservation of pre-existing cycles, creation of two-edge
cycles, and normal forms with zero agents but nonzero cyclic-wire count.
The finite search is reproducible evidence for the example; the explicit
two paths and equal-summary argument establish the stated obstruction.

An independent union-find replay, separate from the checker's component
traversal, compared all 5,673 enabled rewrites across the two-cell and
four-cell matchings and all 10,410 complete normalizations. It also checked
the literal witness paths, preserved pre-existing cycles, and visually
verified the source's numbered rule on page 82 and cyclic-wire definition
on page 71. This review passed on checker SHA-256
`5c4881f28ae3286097c9629751856118d06365300de77d40eaecd087d6d8b0bc`;
the temporary independent review files are
`/tmp/review_interaction_wiring.py` and `/tmp/review_interaction_wiring.json`.
