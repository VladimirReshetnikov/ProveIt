# Paid sink outcomes for periodic routing, without exact odometers

The [builder](routing_balance_outcome_compiler.py) gives a fixed-arity quartic
for termination and the **exact vector of sink outputs** in a finite periodic
stack-routing topology. Its size is independent of the number of firings.
The default two-router example uses **67 operations = 21 M + 46 A**, 11 positive
witnesses, and eight squared residuals. A literal compilation of the imported
canonical-odometer equations on the same topology uses **166 = 48 M + 118 A**,
28 positive witnesses, and 24 residuals. Both accept exactly the same positive
input/output parameter tuples; their witness sets differ.

This is a paid compiler for an explicitly periodic, decidable routing family.
It gives no universal polynomial, no improvement to the separate 75/87
frontier, and no exact-odometer or unique-witness claim. The
[receipt](routing_balance_outcome_compiler.json) contains literal counts,
source digests, and the complete default outcome schedule; the builder emits
the other schedules used in its checks.

## 1. Model and the observable that survives projection

The local primary source is the imported
[canonical-certificate report, Part XIV, manuscript 12](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.tex),
sections “A history-free characterization of exact routing” and “A parametric
single-fold quartic for run-length routing.” Its least-action and last-exit
proofs are mathematical source material, not a Lean formalization. The
argument needed for the present projection is included here.

There are $n\ge1$ active vertices and $s\ge1$ absorbing sinks. Firing an
occupied active vertex removes one chip and sends it to the next destination
in that vertex's fixed infinite stack. Sinks never fire. Initial active loads
are $x_v\ge0$; sinks initially have no chips. Write $R_{vw}(t)$ for the
number of occurrences of destination $w$ in the first $t$ entries of $v$'s
stack. Thus every $R_{vw}$ is nondecreasing and
$\sum_w R_{vw}(t)=t$.

A nonnegative candidate $u$ is balanced when
\[
 u_v=x_v+\sum_a R_{av}(u_a).                                      \tag{1}
\]
**Lemma.** Every balanced candidate proves termination and gives the exact
sink vector, even when it is not the genuine odometer.

Indeed, a legal execution cannot first exceed $u$ at vertex $v$: just
before that firing its count at $v$ is $u_v$, all other counts are at most
their candidate values, and (1) says that its occupancy at $v$ is at most
zero. Repeatedly firing the occupied vertex of least index therefore terminates
after at most $\sum_v u_v$ firings. Let $U\le u$ be the resulting genuine
odometer. Applying the same argument to any complete execution proves
order-independence of $U$.

The candidate sink vector $y_s=\sum_v R_{vs}(u_v)$ is componentwise at least
the genuine vector $Y_s=\sum_v R_{vs}(U_v)$. Summing (1) over all active
vertices, then using the prefix-count row sums, gives
\[
 \sum_s y_s=\sum_v x_v=\sum_s Y_s.
\]
Consequently $y_s=Y_s$ for every sink. Equivalently, the residual flow from
$U$ to $u$ is a circulation with no sink output. The report already uses
this residual-flow fact inside its exact-odometer proof; the new use here is
to omit the entire last-exit certificate when only termination and sink
outputs are requested.

For example, one router with period (self, sink), unit block lengths and one
initial chip has genuine odometer 2. Candidate 3 is also balanced, with the
same sink output 1. Its last exit is a self-loop, so a canonical-height
certificate would reject it. With a self-only router and zero initial load,
arbitrarily many artificial firings are balanced. Thus finite or unique
witness fibers are not retained by this projection.

## 2. A first-incomplete-block chart

Fix a nonempty destination list
$w_{v0},\ldots,w_{v,m_v-1}$ at each active vertex. Its stack repeats
\[
 w_{v0}^{\ell_{v0}}\cdots w_{v,m_v-1}^{\ell_{v,m_v-1}},
 \qquad \ell_{vj}\ge1.
\]
Repeated adjacent destinations and self-loops are allowed. Put
$m=\sum_v m_v$, and let $e$ be the number of blocks with $w_{vj}\ne v$,
including all blocks directed to sinks. Topology is fixed; all lengths are
positive free parameters. Loads and queried sink outputs are supplied as
positive parameters $\widehat x_v=x_v+1$, $\widehat y_s=y_s+1$.

Use positive witnesses $Q_v,P_v,S_v$ and $\widehat b_{vj}$, and compute
\[
 b_{vj}=\widehat b_{vj}-1,\qquad
 a_{v0}=Q_v,\qquad a_{v,j+1}=a_{vj}-b_{vj}.                       \tag{2}
\]
The two local equations are
\[
 a_{v,m_v}-Q_v+1=0,\qquad
 P_v+S_v-1-\sum_j\ell_{vj}b_{vj}=0.                              \tag{3}
\]
Positivity makes the $b$'s nonnegative; the first equation forces exactly
one of them to be 1. If its index is $J$, the second gives
$\ell_{vJ}=P_v+S_v-1$. Hence $q=Q_v-1\ge0$ and
$p=P_v-1\in[0,\ell_{vJ}-1]$. The conceptual candidate odometer is
\[
 u_v=qD_v+\sum_{j<J}\ell_{vj}+p,
 \qquad D_v=\sum_j\ell_{vj}.                                    \tag{4}
\]
This selects the first incomplete block, including at zero and exact period
boundaries. Every nonnegative $u_v$ has exactly one such chart. No separate
activity bit or zero-odometer branch is required.

The routed count contributed by block $j$ is
\[
 E_{vj}=\ell_{vj}a_{vj}-b_{vj}S_v.                               \tag{5}
\]
For $j<J$, this is $(q+1)\ell_{vj}$; for $j=J$, it is
$q\ell_{vJ}+p$; for $j>J$, it is $q\ell_{vj}$. These are precisely the
prefix counts at (4), grouped by supplied block. Although intermediate
expressions may be signed away from zeros, every count is nonnegative at a
positive solution of (3).

The source does not emit (4), $q$, or $p$: they are only quantities in the
proof. Every expression actually used by the compiler is emitted and counted.
For a self-loop block, (5) cancels from conservation, so it need not be
emitted either. Its length and selector remain in (2)–(3).

## 3. Complete polynomial and positive converse

Initialize active residuals to $1-\widehat x_v$ and sink residuals to
$1-\widehat y_s$. For every nonself block, add (5) to its source residual.
Subtract it from its destination residual if the destination is active;
otherwise add it to that sink residual. These equations express
\[
 \sum_{j:w_{vj}\ne v}E_{vj}
 -\sum_{a\ne v}\sum_{j:w_{aj}=v}E_{aj}=x_v,
 \qquad
 \sum_{v,j:w_{vj}=s}E_{vj}=y_s.                                  \tag{6}
\]
Together with (3), there are $3n+s$ residuals. The emitted polynomial is
the sum of their squares.

**Theorem.** For every positive length/load-hat/output-hat tuple, this
polynomial has a positive zero if and only if the routing execution
terminates and its sink vector is the queried output.

At a positive zero, (3) gives the chart and true prefix counts just proved.
Since $\sum_j E_{vj}=u_v$, canceling self-flows in (6) is equivalent to
(1). The lemma proves termination and the exact sink vector. Conversely,
from a terminating execution choose its genuine odometer, divide it into
periods and the first incomplete block, and set $Q=q+1,P=p+1,S=\ell_J-p$
and $\widehat b_j=1+[j=J]$. All these coordinates are positive, and every
residual vanishes. This includes zero initial mass, unvisited vertices,
period boundaries, and adjacent equal destinations.

The canonical comparison uses the report's full natural-coordinate system,
shifted to positive coordinates. In both modes the sink outputs are query
parameters, not witnesses. It has $4n+4m$ witnesses and $6n+2m+s$
residuals. Its existential parameter projection agrees with the new system;
there is no claimed polynomial identity or all-tuple correspondence between
the two systems.

## 4. Paid arithmetic bound

An addition or subtraction costs one A; a multiplication, including by a
fixed numeral, costs one M. Neutral operations and common subexpressions are
folded by the same [literal DAG builder](queue_causality_sentinel_fold.py) in
both compared modes. Closure removes arithmetic rows unused by the final
polynomial. Length parameters have degree one, so every residual has degree
at most two and the complete polynomial has degree at most four.

Before any beneficial folding, the following schedule is sufficient:

| Contribution | M | A |
|---|---:|---:|
| Decode selectors and advance running prefixes | 0 | $2m$ |
| Selection residuals and their squares | $n$ | $2n$ |
| Selected-length sums | $m$ | $m-n$ |
| Position residuals and their squares | $n$ | $3n$ |
| Nonself block counts | $2e$ | $e$ |
| Initialize and update balance/output rows | 0 | $n+s+2e$ |
| Balance/output squares | $n+s$ | 0 |
| Sum all squared residuals | 0 | $3n+s-1$ |

Thus the complete source uses at most
\[
 M\le m+2e+3n+s,\qquad A\le3m+3e+8n+2s-1,
\]
with total at most **$4m+5e+11n+3s-1$**. The declared interface has
$n+m+s$ positive parameters and $3n+m$ positive witnesses. The bound is
independent of numerical lengths, loads, outputs, and firing duration. No
minimality assertion is made, including in degenerate topologies where some
coordinates or constraints cease to affect the polynomial.

The default lists are ($0,1,2$) and ($0,3$), with active vertices 0,1
and sinks 2,3. Here $n=2,m=5,e=4,s=2$, and folding attains the stated
67-operation ledger; the general unfurled bound is 67 as well.

## 5. Why this does not supply a universal routing interface

For any explicit finite periods and finite initial chip mass $C$, every
active occupancy is between 0 and $C$, and each stack position is taken
modulo its finite period length. There are finitely many configurations.
The deterministic rule “fire the occupied vertex of least index” therefore
halts or repeats a configuration. A repeat gives an infinite legal
execution; least action excludes that when any complete execution exists.
This decides termination, and a terminating simulation computes every sink
output. Binary-encoded periods or block lengths may make the procedure
large; they do not make it noncomputable.

Consequently no computable ordinary-input map into this explicit periodic
family can make its termination set universal for arbitrary semideciders.
The report's later “Universal halting with polynomial-time ranks” theorem
uses a different stack interface: a fixed routine computes a prefix rank
by simulating a universal machine on input (c) for
$\lfloor\log_2 k\rfloor$ steps. Its one exceptional sink symbol, if any,
occurs at (2^{T(c)}). Each individual stack is eventually constant, but a
correct finite preperiod/period description cannot be computed uniformly
from (c), since that would decide halting.

To use the outcome lemma for that universal stack, one must replace (2)–(5)
by a complete paid arithmetic relation for its algorithmic prefix counts,
including the ordinary-input and bounded-simulation interface. Its being a
fixed polynomial-time routine is not a literal operation count for an
unbounded arithmetic relation. This packet does not supply that relation.
The useful reduction is exact: the stack-rank interface need only determine
balanced flows and sink outputs, without adding last-exit heights solely to
recover the candidate odometer.

## 6. Reproducible checks and scope of evidence

Run `python routing_balance_outcome_compiler.py` to reconstruct and compare
the receipt; `--write` regenerates it. Author checks pass:

- 1,024 complete source/residual/SOS identities against separately written
  scalar oracles, including 512 signed assignments, on 64 schedules.
- 50,176 candidate odometers across 256 two-router topologies and 1,024
  initial-load cases; 2,186 balanced candidates pass, including 1,262
  deliberately inexact odometers, all with correct sink outputs. All 924
  terminating executions also give canonical witnesses, and 4,372 altered
  sink queries are rejected.
- 192 additional contexts with variable block lengths, including 158
  terminating cases; both compilers accept their actual outcomes.
- 2,187 complete positive assignments in a small adversarial chart, with
  nine zeros, plus the explicit circulation fixture from Section 1.

These are finite source and semantic audits. The unbounded-duration theorem
rests on the preceding least-action, flow, and chart proofs.

Root full proof/source review, comparison with the actual imported Part XIV,
and fresh default replay passed with no findings. A separate independent
full proof/source review and fresh replay also passed. That reviewer used
its own executor and residual formulas for 512 complete source/SOS identities (256 signed) across 64
ledgers and both modes. Its separate variable-length chart construction and
highest-index physical firing simulation checked 2,041 balanced candidates,
including 826 inexact odometers, 20,125 physical firings, and 4,082 rejected
wrong sink queries, without using the author oracle, witness constructor,
or simulator. All four local links resolve. No universal arithmetic bound
is inferred from the small default ledger.
