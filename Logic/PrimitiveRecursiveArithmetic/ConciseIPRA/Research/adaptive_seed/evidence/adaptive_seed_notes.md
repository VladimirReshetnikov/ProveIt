# Adaptive initializer circuits: a broader obstruction

## Attribution and contribution

The existing counter-congruence and transient-seed proposals already prove
that the particular recursor

    B(0;h) = 1 + h(0,0)
    B(n+1;h) = h(n,B(n;h))

has the one-coordinate majorant property. The transient-seed proposal also
explicitly proves composition closure and excludes an injective pairing term.
Those facts are inherited, not new results here.

The additional statement is that the obstruction persists when the initializer
is any fixed finite adaptive query circuit for the same update. The circuit
may combine answers using arbitrary fixed primitive-recursive operations,
including addition, multiplication and maximum. The language may also be
enlarged by arbitrary fixed unary primitive-recursive functions, bounded
Boolean tests, minimum, one-sided data gates, and other primitive operations
already possessing a one-coordinate majorant. The new coverage concerns
these initializer circuits; no global novelty claim is made.

## Exact grammar and semantics

A circuit is a finite directed acyclic graph. A node is a numeral, an
application of a fixed primitive-recursive function to earlier nodes, or a
query H(a,b) with earlier node values as arguments. There are no ordinary
input nodes. One node is its output.

For an update term h(u,v,p), regard h_p(a,b)=h(a,b,p) as the queried oracle.
The passive parameters p reach the circuit only through this oracle. The
circuit does not receive an independent seed or the actual recursion counter.

For every fixed such circuit P, allow the term constructor

    R_P(0;u,v.h) = P^(h_p)
    R_P(n+1;u,v.h) = h(n,R_P(n;u,v.h),p).

Each fixed term denotes a primitive-recursive function. The circuit and the
update body are finite static syntax. There is no object-level universal
primitive-recursive evaluator and no function quantification.

Other initial primitives are constants and projections and may include any
fixed PR function f admitting either a constant bound or a bound
f(x_1,...,x_k) <= F(x_i), for a fixed coordinate i and a unary PR function F.
Arbitrary nesting and ordinary term substitution are allowed.

For example, a permitted initializer first computes q=h(0,0,p) and returns
q+h(q,q+1,p)^2. Its second query is adaptive and its combination may grow
rapidly, but the theorem still prevents two independent unbounded controlling
coordinates from reaching its value through the one update.

## The theorem

Every fixed term in this grammar has either a constant bound or a bound

    t(x_1,...,x_k) <= F(x_i)

for one fixed input coordinate i and one unary PR function F. The coordinate
and bound may depend on the term. No uniform PR evaluator for majorant values
from arbitrary term descriptions and numerical inputs is asserted. Producing
a finite description of a bound is distinct from uniformly evaluating it.

## Circuit lemma

For a fixed r-ary PR function g, its diagonal box envelope

    g_hat(z) = max { g(z_1,...,z_r) : all z_j <= z }

is unary PR and nondecreasing. This permits arbitrary nonmonotone combining
operations in the circuit.

1. If every oracle answer H(a,b) is bounded by M, traversing the circuit in
   topological order gives a unary PR output bound C_P(M). Constants have
   constant bounds; oracle nodes have bound M; ordinary operation nodes use
   g_hat of the largest predecessor bound.
2. If H(a,b) <= F(a), then the same traversal gives a constant output bound
   depending only on P and F. At a query node use the monotone envelope of F
   applied to the already computed constant bound on its first argument.
   The analogous statement holds for a bound F(b).

Adaptive queries cause no difficulty because their argument nodes precede
them in this finite acyclic ordering.

## Structural induction proof

Known primitives and composition preserve the claimed property by composing
monotone envelopes with the bound on the controlling argument term.

For a recursor, apply the induction hypothesis to the body h as a function
of its counter u, state v, and passive parameters. Replace its unary bound
F by its nondecreasing envelope.

- **Passive parameter p_i controls h.** Every oracle answer is at most
  F(p_i). Thus the initial state is at most C_P(F(p_i)), and every subsequent
  state is at most F(p_i). Their maximum is a unary PR bound in p_i, entirely
  independent of the actual counter term.
- **The counter u controls h.** The second circuit lemma bounds the initial
  state by a constant b. At positive counter n, the state is at most F(n-1),
  so M(n)=max(b,F(n)) bounds all states and is monotone PR.
- **The previous state v controls h.** Again the initial state is bounded by
  a constant b. With K(z)=max(z,F(z)), the recursive state at n is at most
  K iterated n times starting at b. This is a monotone unary PR function of n.
- **h has a constant bound.** This is the passive-parameter case with a
  constant M and gives a constant bound on the entire recursor.

In the counter and state cases, the actual counter n is a smaller term.
Compose its constant or one-coordinate bound with the monotone bound in n.
This exhausts the structural induction.

## Consequences and limits

The old no-addition, no-general-selector and no-injective-pairing consequences
now apply to this larger family. For addition or maximum, fixing the putative
controlling coordinate leaves an unbounded other input. For an injection from
N^2 to N, fixing that coordinate would place infinitely many distinct inputs
in a finite bounded range.

The hypothesis is meaningful: if the initializer is allowed an independent
passive input y, choose h(u,v,x,y)=x and initialize with y+h(0,0,x,y). At
counter zero this yields x+y. Two separately chosen update oracles h_1=x,
h_2=y likewise allow their answers to be added. These relaxations escape this
obstruction, without thereby establishing a complete PR basis.

This is a standard-function term-definability obstruction. It does not
exclude graph definitions using quantifiers, relational interpretations,
different domains, quotients, or bi-interpretability achieved by other means.
It is not an impossibility theorem for every seed-removal strategy, and it
is not a new positive axiomatization or a smaller proof checker.

## Source fragments checked for attribution

- `baselines/ipra_counter_congruence_2026-11-10/ipra_counter_congruence_2026-11-10/theory/obstructions.tex`
- `baselines/ipra_transient_seed_2026-11-10/ipra_transient_seed_2026-11-10/theory/obstruction.tex`
- `baselines/ipra_generated_assumptions_2026-11-10/ipra_generated_assumptions_2026-11-10/ipra_generated_assumptions.tex`, section “An obstruction to folding the initializer into the update.”

The full inclusion-ready proof is `adaptive_seed_obstruction.tex`.
