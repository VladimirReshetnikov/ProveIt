# Review of the imported computational-substrate reports, 2 October 2026

The three imported report collections contain useful explicit compilers, but
none of the newly reviewed claims lowers the established **87-operation fixed
universal polynomial**. The principal distinction is between a polynomial
whose size depends on a supplied execution horizon and one fixed polynomial
that accepts arbitrarily long computations. Another is between existence of
witnesses, our objective, and preservation of unique witnesses, an additional
requirement in many of the reports.

The review found two inaccurate README summaries, both corrected, and concrete
redundancies in the bounded FRACTRAN and priority-reaction compilers. No
mathematical defect was found in the main constructions actually reviewed.
This is a targeted mathematical/source review with finite executable checks,
not a formal verification or a certification of every claim in these large
collections.

## Sources and scope

The reviewed source collections are:

- [Canonical Diophantine certificates](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/README.md),
  through the routing addition at 781594d88 and the heaps/assembly/pumping/
  reactions addition at 0744012ba. Its
  [article](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.tex)
  has 14 Parts from 12 manuscripts.
- [Probabilistic, quantum and continuous computation](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/probabilistic-quantum-and-continuous-computation/README.md),
  especially 176e31c5c and the rational-tubes addition 4681763c7. Its
  [article](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/probabilistic-quantum-and-continuous-computation/article.tex)
  contains the precise observation predicates and domain restrictions.
- [Liveness beyond halting](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/liveness-beyond-halting/README.md),
  merged at 2a34b1740; its
  [article](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/liveness-beyond-halting/article.tex)
  separates finite paths from infinite recurrence and deadline predicates.

Three independent reviewers divided the discrete, later/order-free, and
analytic/quantum/liveness material. The root reviewed their findings, the
relevant source passages, the quantitative implications and both documentation
fixes. The mathematical reading covered the core resource/commutation,
polynomial-sign, memory, queue, scheduled-rewriting and counter-schedule
constructions; the later heap, assembly, priority, reaction and routing proofs;
and targeted rotation, contraction, neural, equilibrium, rational-tube and
liveness arguments. Literature dependencies were checked selectively, not
reproved wholesale. No report was treated as an instruction or as formal
verification merely because it resides beside Lean/Rocq developments.

## Corrected findings

1. **The fixed-degree summary contradicted the article.** The probabilistic
   report's README said no fixed MRDP polynomial had a stated degree. Its
   fixed-quartic corollary, label `pqc:tu:cor:fixedquartic`, explicitly gives
   degree at most four by standard circuit quadratization. Commit 29438ffd1
   corrects the distinction: the fixed polynomial is not expanded or given
   a numerical witness/operation count; its degree can be bounded, and the
   multiplicity of the original MRDP witnesses remains uncontrolled.
2. **The rotation-density hypothesis was ambiguous and could be read
   incorrectly.** The same README said density holds for a nontrivial
   presentation. The actual theorem, label `pqc:dr:thm:compiler`, requires a
   nontrivial relator kernel N. For the nontrivial free group presentation
   `<a,b | >`, N is trivial, the fiber product is diagonal, and its spin image
   fixes quaternion 1, so it is not dense in SO(4). Commit e61a07cdb states
   the correct condition and the article's dummy-generator padding. The
   underlying article already had the correct theorem.

Both are documentation corrections. Neither changes a compiler or invalidates
an article theorem. No other actionable correctness finding emerged in the
reviewed material; unreviewed dependencies retain their original status.

## What each substrate contributes to arithmetic compression

| Substrate | Useful result | Remaining cost or obstruction |
|---|---|---|
| Causal traces and counter schedules | Exact resource summaries, commutation, repetition saturation and canonical inactive branches | General trace size depends on length/height/schema. The depth-two universal schedule theorem invokes MRDP first, so it is not an independent route to a smaller universal polynomial. |
| Polynomial trajectories | A sign-tower certificate independent of numerical duration for fixed polynomial degree | Arbitrary branching universal histories have not been given fixed-degree polynomial trajectories. A variable trajectory degree/circuit cannot be counted as a fixed primitive. |
| Random-access memory and heaps | Exact large-base product fingerprints, chronology, birth-order names and pointer-range checks | Products and witness lists grow with access-log length. Fresh-name normalization does not identify arbitrary schedules or final graph isomorphisms. |
| Queues, tag systems, SKI | First-failure causality; two-coordinate word memory; local subterm sharing | Consumed-symbol coordinates, product factors and scheduled context paths still depend on the external horizon. These reports do not supply a fixed-size, fully charged decoder for an existential unbounded schedule. |
| Self-assembly | Earliest-arrival ranks exclude circular support; terminality checks the exterior halo | The finite spatial domain is compiler data. Low degree on each domain does not make one fixed-arity universal polynomial. Nonnegative glues are essential. |
| Priority/FRACTRAN pumping | Exact enabling intervals and a sharp capacity threshold; fixed-word powers independent of repetition count | Priority can fail in the interior, so endpoint tests are insufficient. The word schema and valuation dimension remain fixed; the raw-integer interface still needs arithmetic compilation. |
| Conservative priority reactions | A literal four-phase zero test and a 61-species/62-rule compiler | Every fixed-fuel closed system is finite-state; universality quantifies over fuel. Bounded trace and minimum-fuel polynomials depend on a cutoff. Priority is an actual semantic feature, not finite-rate chemistry. |
| Periodic routing | Fixed-topology certificates independent of the number of firings; exact least action | Explicit finite periods are decidable. The universal one-router construction puts bounded universal simulation inside its rank algorithm; no small arithmetic rank polynomial is supplied. |
| Rational matrix/rotation words | Exact denominator decoding, spin lifts, state-transfer and word-membership reductions | A low-dimensional state space is not a small equation. The universal presentation, hard target words and input loader must be instantiated and charged. Density or approximate synthesis is insufficient. |
| Neural networks and real/2-adic contractions | Exact finite-event certificates; useful complementarity and scale arguments | The explicit families grow with horizon. Rational tied-weight synthesis concerns H10(Q), not integer solvability. Exactness can require unbounded precision despite contraction. |
| Polynomial flows and chemical lifts | Complete rational-tube checking and invariant lifts avoiding auxiliary blow-up | The 17-witness constant-flow example is not universal. A concrete universal finite-open-event front end and a compressed checker are still required. |
| Probabilistic equilibria and liveness | Precise quantifier boundaries and finite-prefix certificates | Exact equilibrium equality, almost-sure halting and infinite recurrence are generally outside a single existential Diophantine predicate. Finite reachability or suitable strict cuts are different targets. |

The table is a transfer assessment, not a ranking by physical plausibility or
a claim that these substrates cannot yield future improvements.

## Concrete simplifications found in the review

### Bounded FRACTRAN: two redundant residuals and one linearization

The actual compiler's division gadget has natural coordinates q,rho,s,u,z and
six equations:

    n=bq+rho, rho+s=b−1,
    z(z−1)=0, z*rho=0,
    rho=(1−z)(u+1), z*u=0.

Because u+1 is strictly positive, the fifth equation and rho>=0 force
z<=1. With natural z, this already gives z∈{0,1} and z*rho=0. Thus the two
explicit residuals for those facts can be deleted without changing any
natural witness tuple. The retained z*u=0 is necessary for uniqueness when
rho=0. It also permits replacing the fifth residual by the linear expression

    L=rho−u+z−1,

because the old residual equals L+z*u. This is full natural-zero-set
equivalence, not equality of the complete polynomials off zero.

For horizon T and r fractions, the residual count becomes
`T(6r+3)+2`, down from `T(8r+3)+2`, with the same `T(7r+2)+1` natural witnesses.
The first-halting extension keeps its additional 3r witnesses and 2r residuals.
The [guarded FRACTRAN transfer](fractran_divisibility_residual_projection.md)
separately charges a literal sparse-polynomial evaluator. It saves 7rT gates
for deletion, or 9rT for deletion and linearization, under that declared
schedule. The six-step `(3/2,5/3)` example drops from 515 to 407 operations,
with all 97 natural witnesses retained; its first-halting form drops from
534 to 426 with 103 witnesses. These counts do not include a natural-to-
positive coordinate conversion. Neither stage is a fixed-arity universal
construction. The signed-domain extension is false:
q=2,rho=−1,s=1,u=0,z=2 at n=b=1 satisfies the reduced gadget but violates the
deleted Boolean and zero-test equations. Nonnegative rational coordinates
also fail: rho=z=1/2,u=0 satisfies both retained local equations but not
the deleted ones.

### Bounded reactions: aggregate only after the required signs are proved

The same zero-test redundancy occurs in the reaction compiler. Natural
selectors summing to 1 are already Boolean. Once the retained zero and enabling
relations prove e_j∈{0,1}, all terms in

    F=sum_j s_j(1−e_j)
      +s_low*sum_(j!=low)e_j+s_idle*sum_j e_j

are nonnegative. One equation F=0 can therefore replace the separate
eligibility, priority and idle equations. Keep F squared in the full finalizer:
F need not be nonnegative on arbitrary off-zero assignments where the enabling
relations fail. A complete one-step, one-reaction source demonstrates the
failure: set all initial species counts to 1, retain its legal trace, and
change the enabling flag from 1 to 2. Its only nonzero retained residual is
1 and F=−1, so the incorrect unsquared finalizer is zero while the correct
sum of squares is 2. With all other constraints retained this gives the same full
natural zero set and a residual count

    (3d+R+2)T+d+1,

or 247T+62 for d=61,R=62, compared with 616T+62 in the imported source.
The witness count remains 308T+61. This is a bounded residual-count improvement;
the [guarded reaction transfer](reaction_priority_residual_projection.md)
checks its actual imported source, including arbitrary initial markings and
the low-priority rule at different indices. It does not claim a universal
gate saving.

### Avoid paying for uniqueness when only existence is needed

The existing [routing outcome compiler](routing_balance_outcome_compiler.md)
already makes this distinction concrete: balancing a candidate odometer is
enough for termination and the exact sink outputs, even when the candidate
contains artificial circulations. Its default 67-operation relation replaces
a 166-operation canonical-odometer relation on the same decidable topology.
It deliberately gives up exact odometers and unique witnesses.

The universal one-router boundary illustrates the same point. If a fixed
polynomial G(c,k,b,z) represents its rank graph, mere halting requires only
`exists k,z: G(c,k,1,z)=0`. The report's second rank query at k−1 is needed
to identify the unique first hitting counter, not for existence of a hit.
With the program/input code kept as a separate Cantor-pairing coordinate c,
the noncanonical wrapper uses r+2 natural witnesses instead of the report's
2r+3, where r is the number of G auxiliaries. This observation supplies no
numerical improvement: G itself has no printed arithmetic circuit, and may
already contain all of the original universal-computation cost.

## Executable evidence and important boundaries

Fresh tests ran in copies with the manuscripts' original module names; no
imported source receipt was overwritten. The README reproduction instructions
of each collection provide the delivered layouts.

| Group | Fresh suite entry points | Selected exact checks |
|---|---:|---|
| Discrete manuscripts 01–07 | 9 | 4,914 FRACTRAN and 1,875 SKI certificates; 92,610 cyclic-tag and 194,940 deletion-tag candidates; 79,631 quartic queue assignments; both memory backends and counter-schedule frontend |
| Later discrete manuscripts 08–12 | 5 | 40,347 sorting permutations; 476,656 semilinear assignments; 114,875 priority checks; 67,943 reaction microsteps; 123,201 candidate routing odometers |
| Exotic/liveness suites | 11 | 121,822 2-adic checks; 53,472 neural assertions; 113,686 equilibrium checks; 302,498 local quadratic-recurrence checks; 17,197 deadline checks; rotation, landscape, contraction and tube suites |

Independent review of the new FRACTRAN wrapper also caught an exactness
bug before publication: value-based Python equality accepted floating-point
coefficients equal to the canonical integers. At endpoints 2^100, rounding
could hide an endpoint error of one. The new wrappers use recursive
comparison of both values and types, with a regression for this case. This
is an implementation guard repair, not a change to the algebraic theorems.

Both new packets passed independent proof/source review and fresh receipt
replays. FRACTRAN's separate evaluator checked 144 source forms, 48 ledgers,
2,304 outputs and 477 successful/wrong-endpoint pairs. The reaction review
checked 312 source forms, every low-priority position and 14,580 arbitrary-
marking/selector cases. The linked proof notes preserve the complete counts,
domain counterexamples and guard-repair provenance.

Additional independent export evaluation checked the strict-contraction
quartic and all eight supplied rational-tube certificates. These finite checks
support implementation and examples. They do not establish infinite-run
hardness, universal-machine existence, an expanded fixed MRDP polynomial, or
formal proof-assistant status.

Two literature interfaces were also checked against primary sources. The
reaction table's q27 zero branch follows q29 in the
[Alhazov–Verlan flowchart](https://arxiv.org/pdf/1009.2706), resolving its
conflicting printed instruction list in the same way as the report. The exact
autonomous rational-network halt-coordinate contract appears in Theorem 2 of
[Siegelmann–Sontag](https://binds.cs.umass.edu/papers/1995_Siegelmann_JComSysSci.pdf).
These checks validate those specific interfaces, not every external theorem
used by the reports.

## Consequences for the ongoing universal-equation work

The highest-priority transferable idea is to remove explicit Boolean and
nonnegativity constraints when retained natural-domain equations already force
them, and then simplify residuals modulo those retained equations. Such a
rewrite needs both implications, a domain statement, complete source counts
and an off-zero correction. Conditional nonnegative aggregation is another
candidate; signs must be proved before combining terms.

This does not immediately shorten the current 87-operation construction,
whose old native slack comparisons have already been projected or merged
into one eight-unit product. A new saving there needs an actual source change,
not the count of redundant rows in a different bounded compiler.

Continue numerical universality work on instantiated tables and paid input
interfaces. The reviewed [763-operation sparse-TM source](gpcp_first_padding_units763.md)
and [32-base C2 frontier](tseytin_transport_query_factor_partitions.md) remain
separate, fully counted routes. Matrix/rotation alphabets, universal rank
routines and flow front ends should enter that comparison only after their
concrete data and all arithmetization costs are supplied. The review advances
those obligations and bounded compilers; it does not settle the open global
arithmetic-complexity goal.
