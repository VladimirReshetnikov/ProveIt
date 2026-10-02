# A guarded quadratic topology relation for interaction-combinator annihilation

This [guarded compiler](interaction_combinator_quadratic_topology.py) supplies a concrete relation over **nonnegative integers** for one externally selected delta–delta interaction, retaining the complete port matching and the number of port-free cyclic wires. It also composes such relations along an externally fixed finite deletion schedule. It is not a compiler for the universal six-rule system, an integer-domain equivalence, a paid input loader, or a fixed-arity encoding of arbitrarily long computations.

The useful new lemma is local: among the four removed auxiliary ports, a surviving wire takes either a direct gluing edge or a path of the form gluing–old wire–gluing. Two common intermediate products are enough to count all newly created cyclic components. Factoring the routing through shared witnesses turns the complete relation quadratic and reduces the literal arithmetic cost in the four-cell example.

Source conventions are those of [Lafont's primary paper](https://www.i2m.univ-amu.fr/perso/yves.lafont/pub/combinators.ps), *Interaction Combinators* (1997): journal page 71 allows cyclic wires with no ports; page 82's numbered delta annihilation preserves auxiliary labels. The universal three-symbol/six-rule table is Figure 2 on page 81. The compiler pins and executes the published [local wiring oracle](interaction_combinator_wiring_obstruction.py), SHA-256 `5c4881f28ae3286097c9629751856118d06365300de77d40eaecd087d6d8b0bc`. Only its terminating delta fragment is simulated.

## 1. Exact graph domain

Fix an even number n of labelled delta cells, with P=3n ports. Cells have ordered ports 0 (principal), 1 and 2. For every unordered pair of distinct ports u,v introduce a source coordinate x_uv in N={0,1,...}. Impose

    sum_{v != u} x_uv = 1                    for each port u.

These linear equations and nonnegativity force x_uv in {0,1}, and define a perfect matching. No separate Boolean constraints are needed. Self-wires between different ports of one cell are allowed. A separate L in N counts cyclic components without ports. This is the exact abstract-net topology up to the identities of the otherwise indistinguishable port-free cycles; no graph embedding is supplied or needed.

Fix two distinct cell identifiers and additionally impose that their principal ports are joined: x_principal,principal=1. The choice of pair is external to this relation. Remove their six ports. The remaining s=P−6 ports have successor edge coordinates y_uv; L' counts successor cyclic wires.

Number the removed auxiliary ports 0,1,2,3, corresponding to first-cell labels1,2 and second-cell labels1,2. These are local names, distinct from the global principal-port label. Gluing is the involution J=(0 2)(1 3). Write e_ij for the old matching coordinate between removed auxiliary ports i,j, and x_ui for the old edge between surviving port u and removed auxiliary port i.

## 2. Ten local patterns and the cycle formula

The restriction of the old matching to the four auxiliary ports is a partial matching. It has only ten possibilities: no internal edge, one of six internal edges, or one of three perfect matchings.

A newly created cyclic component has no surviving endpoint. A single old internal edge creates a two-edge cycle exactly when it equals one of J's two gluing edges. If all four auxiliaries are internally matched, the matching equal to J creates two cycles; either other perfect matching creates one four-edge cycle. Therefore the exact increment is

    c = e02 + e13 + e01*e23 + e03*e12,
    L' = L+c.                                             (1)

Computing c costs 2M+3A; computing the complete loop residual L'−(L+c) costs 2M+5A. Pre-existing cycles are retained. In particular, a two-edge cycle is not discarded as a duplicated edge.

For a path between surviving endpoints, the first and last edges are old edges incident to removed auxiliary ports. In between, either there is one J edge, or there are two J edges and one old internal edge. There cannot be a longer simple path on these four auxiliary vertices. Consequently, for u<v surviving,

    y_uv = x_uv
         + x_u0*x_v2 + x_u2*x_v0 + x_u1*x_v3 + x_u3*x_v1
         + e23*(x_u0*x_v1 + x_u1*x_v0)
         + e12*(x_u0*x_v3 + x_u3*x_v0)
         + e03*(x_u1*x_v2 + x_u2*x_v1)
         + e01*(x_u2*x_v3 + x_u3*x_v2).                  (2)

The principal-pair equation and perfect-matching domain ensure these cases are disjoint when evaluated on a valid net. An unaffected edge contributes the x_uv term. No spurious duplicate path survives. Equation (2), together with (1), is therefore exactly the oracle's path/cycle gluing; it is not merely an implication on a selected test fixture.

## 3. Shared quadratic routing witnesses

For each surviving v except the first in the fixed port order, supply four natural witnesses z_v0,...,z_v3 and impose

    z_v0 = x_v2 + e23*x_v1 + e12*x_v3,
    z_v1 = x_v3 + e23*x_v0 + e03*x_v2,
    z_v2 = x_v0 + e03*x_v1 + e01*x_v3,
    z_v3 = x_v1 + e12*x_v0 + e01*x_v2.                  (3)

Then replace (2) by

    y_uv = x_uv + sum_{i=0}^3 x_ui*z_vi.               (4)

Only the later endpoint v uses routed witnesses, so none are needed for the first surviving port. Every value in (3) is nonnegative; the definition gives a unique helper tuple for each valid source. Expanding (4) gives (2) exactly, even off the matching domain. Thus these witnesses do not change the represented source/successor relation.

The source row sums and principal-edge condition, four equations (3) per helper endpoint, all equations (4), and (1) are a quadratic system. Sum their squares to obtain one quartic polynomial. Its natural zeros are **exactly** valid source matchings with the selected active pair and their actual successor matching/cycle count, with uniquely determined routing witnesses. No successor row sums or successor Boolean constraints are needed: the path/cycle proof already establishes that the forced successor coordinates constitute a matching. Omitting source row sums is justified only when validity has been established by a previous certified step.

The formal quartic degree is exact: the loop residual has a nonzero quadratic term, and highest homogeneous parts of real squares cannot cancel. For the direct cubic variant with surviving ports, the update residual has a nonzero cubic term, so its sum-of-squares degree is exactly six. These are formal degrees in all table coordinates, before specializing a source net.

## 4. Fully charged local schedules

Write K=binomial(s,2) and v=max(s−1,0). A is one addition/subtraction and M is one multiplication, including a square or numerical multiplication. The emitted schedule shares only the indicated helpers; no claim of circuit optimality is made.

For the quadratic relation, the certificate costs

    M = 8v + 4K + 2,
    A = P(P−1) + 12v + 5K + 6,
    E = P + 4v + K + 2 residuals.

The source row-sum constraints cost P(P−1)A. Each helper equation costs 2M+3A. Each successor-edge equation costs 4M+5A. The principal-edge residual costs1A and the cycle residual costs2M+5A. Combining the E residuals as their sum of squares adds E M and E−1 A.

There are binomial(P,2)+1 supplied source coordinates, K+1 successor coordinates and 4v quantified routing helpers. If the source graph is instead included among witnesses, its coordinates must be counted there too; they are not a constant-size numerical input.

For the direct cubic variant, omit all helpers and use (2). Its certificate costs

    M = 16K+2,
    A = P(P−1)+13K+6,
    E = P+K+2.

|Selected rewrite|Helpers|Residuals|Certificate|Single polynomial|Degree|
|---|---:|---:|---|---|---:|
|4 delta cells to 2, shared routing|20|49|375=102M+273A|472=151M+321A|4|
|4 delta cells to 2, direct cubic|0|29|575=242M+333A|632=271M+361A|6|
|2 delta cells to 0|0|8|38=2M+36A|53=10M+43A|4|

The shared-routing example saves160 literal operations, at the cost of20 additional quantified coordinates, relative to the displayed unshared cubic schedule. The two variants have67 supplied source coordinates; successor plus helper counts are36 and16 respectively. This is a local, fully charged tradeoff, not a universal Diophantine bound.

## 5. Whole finite histories and the remaining memory cost

Fix an entire deletion schedule of T ordered cell pairs, each drawn from the surviving cells at that stage. Retain an adjacency table and cycle count at each time. Impose source matching row sums only at time0, then impose the active-pair, routing, successor and cycle equations at every step. By induction the previous certified successor supplies the next step's matching validity, so duplicate row-sum tests can be deleted. All intermediate tables and all helper witnesses remain paid.

Let s_t=P_t−6, v_t=max(s_t−1,0), K_t=binomial(s_t,2), with P_t=P0−6t. The combined quadratic certificate has

    M = sum_t (8v_t+4K_t+2),
    A = P0(P0−1) + sum_t (12v_t+5K_t+6),
    E = P0 + sum_t (4v_t+K_t+2).

One sum of squares again costs E M+(E−1)A. The four-cell schedule AB then CD costs484=155M+329A, has51 residuals and37 successor/helper coordinates beyond67 source coordinates, and is quartic. The published witness net A satisfies it and ends with exactly two cyclic wires. Net B cannot satisfy that same schedule because the required second principal edge is absent. This is an exact scheduled history relation; it does not quantify over possible scheduling choices at no cost.

For delta-only histories T<=n/2, so every run terminates. The universal system also has gamma/epsilon interactions, including the growth rule replacing two cells by four. Supporting all six rules requires cell types, rule choice, allocation, and the corresponding topology updates. An unrolled complete adjacency representation with a fresh identifier pool grows with the horizon; even the present known-schedule relation has O(T*P0²) graph coordinates/gates as an upper bound. Compressing arbitrary tables and history into fixed arity, selecting a redex arithmetically, and loading ordinary numerical input all remain separate unpaid obligations. The four-port path/cycle kernel is transferable; the global fixed-size compiler is not supplied here.

## 6. Domain obstruction and replay evidence

Nonnegativity is essential to the row-sum shortcut. For two cells, set the principal edge to1, all principal-to-auxiliary edges to0, and on the four auxiliaries set

    e01=e23=e02=e13=1,
    e03=e12=−1,
    L=0, L'=4.

Every signed row sum is1 and (1) gives c=4. All emitted residuals vanish, although the supposed source is not a matching and a two-cell annihilation cannot create four cycles. The receipt records this complete signed counterexample. No zero-set equivalence over Z or conversion from natural witnesses to integer witnesses is claimed.

## 7. Complete guarded source and replay

The [receipt](interaction_combinator_quadratic_topology.json) contains complete
literal packets for the four-cell quadratic step, its direct cubic comparison,
the two-cell quadratic step, and the fixed two-step quadratic history. Each
packet includes every arithmetic gate of its certificate and final sum of
squares, all residual names, the complete sparse integer residual polynomials,
all source/successor/helper coordinate names, exact ledgers, and a nonzero
highest homogeneous residual part certifying the exact formal SOS degree.
Sparse terms have the form `(coefficient, ((coordinate, exponent), ...))`;
monomial factors are sorted by coordinate name, and omitted coordinates have
exponent zero. The degree certificate uses these expanded integer residuals,
not only a syntactic degree upper bound along the gate schedule.

`build_step(cells=(0,1,2,3), pair=(0,1), mode='quadratic')` builds one complete
step. Setting `mode='cubic'` obtains the displayed direct comparison.
`build_history(cells=(0,1,2,3), pairs=((0,1),(2,3)))` builds a fixed quadratic
schedule. Cell identifiers must be an ordered tuple of distinct natural
integers of positive even size. Pairs must be ordered tuples of two distinct
currently surviving cells. A nonempty history must consume existing pairs;
repeated/deleted identifiers are rejected. These exact type checks occur
before cache lookup, so Python's `True == 1` and `1.0 == 1` do not merge
invalid public requests with valid cached instances.

The public step builder always includes initial matching row sums. Their
omission is available only inside the history constructor after a previous
certified transition. `checked` requires the entire exact-type canonical
packet: source gates, coefficients, sparse exponents, domain, metadata,
leading terms, history mappings and local sources all participate. Changing
an operation, dropping rows or changing the claimed domain fails validation.
Public builders and source/ledger accessors return defensive copies; internal
memoized objects are private.

`polynomial_source(packet)` exposes the complete final SOS schedule and
`residual_polynomials(packet)` exposes its expanded residuals. `ledger` and
`degree_certificate` return the verified count and degree records.
`execute(packet, values)` and `evaluate(packet, values)` require exactly the
complete named natural assignment; the latter returns the integer polynomial
value. `step_values` and `history_values` construct complete assignments from
literal source nets using the pinned oracle, preserving pre-existing cyclic
components. Neither constructor accepts an unavailable scheduled redex.

`evaluate_integer` and `execute(..., allow_signed=True)` deliberately expose
signed algebraic evaluation for the displayed counterexample and off-domain
polynomial checks. They do not claim signed coordinates encode graphs.
Boolean and float coordinates, missing or additional coordinates, and
non-Boolean domain flags are rejected.

The executable loads the exact oracle from a sibling file after checking its
SHA256, without a workspace-specific absolute path or an unpinned import.
Only standard-library Python is required. The mathematical source remains
Lafont's primary paper at the pages cited above; the finite executable is an
oracle for its delta annihilation fragment, not a substitute universality
proof.

From the repository root:

```sh
python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/interaction_combinator_quadratic_topology.py
```

Normal execution recomputes and compares the saved receipt. `--write`
regenerates it. Successful execution prints
`PASS_INTERACTION_COMBINATOR_QUADRATIC_TOPOLOGY`.

The exhaustive audit enumerates all 10,410 perfect matchings on two or four
delta cells and checks all 5,673 enabled rewrites against the literal pinned
oracle. Across the quadratic and cubic sources it verifies 11,346 complete
natural polynomial zeros, rejects 11,346 wrong cycle counts and 11,340
altered successor edges, and observes all ten internal partial-matchings.
The fixed AB-then-CD history also passes on every one of the 189 four-cell
matchings for which that whole schedule is enabled. Four cycle-preservation
checks include an existing count of 10^30. There are 48 signed comparisons
between complete sparse residuals and the literal arithmetic schedule, and
each of the 20 routing helpers is independently perturbed and rejected.
The guard replay rejects 166 malformed inputs and checks four cold-cache
copy-isolation cases. Literal A/B assignments and the complete signed-domain
counterexample are saved in the receipt.

These checks support the explicit all-size path/cycle and history-induction
proofs. The local costs are fully paid for the stated tables and externally
fixed schedules. The packet supplies no fixed-size universal equation and
no improvement to the project's global 87-operation benchmark.
