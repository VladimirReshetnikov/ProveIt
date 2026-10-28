# Closing-cutoff composition: streamed separators plus the explicit schedules

## New strongest polynomial-space result after reviewing the five late packets

The closing-cutoff `sat_adaptive_contraction_2026-10-26` packet proves streamed recursive conditioning of the exact pair-index mode graph. It supersedes unrestricted mode-tuple enumeration as the polynomial-space evaluator. Its fixed-r16 theorem has coefficient55.70947831891. The two late variable-arity schedules, when composed with this same streamed evaluator, give55.40466590661 and55.40905513610. Therefore63.758994 is no longer a strongest polynomial-space result; it is an intermediate enumeration coefficient only.

Composing the streamed evaluator with our already certified explicit generic schedule gives

    T <= poly(s+L) 2^{(C_stream+o(1)) s/sqrt(log_2 s)},
    C_stream=55.331622120479864...,

in polynomial space, under the unchanged generic degree-s^.9 normalized interface. The exact checker proves

    C_stream < 1029779221771/18607088500
             =55.343382806557834... <55.35.

It also proves lower enclosures above55.4 for each of the two stronger late variable-arity/streamed compositions. Thus the improvement does not rely on comparing only with the weaker55.709 fixed-r16 display.

For initial degree<=ceil(s^.51), the independently certified degree-sensitive schedule gives

    C_stream,.51=25.16376541522859...,
    C_stream,.51 <1326135054955358/52688987071875
                =25.16911272456857... <25.2,

again in polynomial space. The narrower s^(1/12)-degree cached result15.391933 remains a separate resource/promise case; do not suppress it or compare it as though it had the same degree and space assumptions.

## What is inherited and what changes

The late packet's new streamed identity is imported, with its short proof restated below. Its ordinary exact pair-budget indexing and weighted entropy are the same interfaces used by the joint-Cauchy cached evaluator. No graph packing, tensor description, degree, precision, creation-time representative, or local Cauchy factorization changes. Only the number of paid recursive child evaluations changes.

The contribution here is an explicitly verified composition and coefficient improvement beyond the late packets and their straightforward variable-arity compositions. Variable alphabets, streamed conditioning, and the slope-four basis themselves are not claimed as newly invented in this iteration after the late source review.

## Streamed identity and paid call count

Fix an exact pair-weight array and its Cartesian product of nonempty pair lists I_e. Each group function Z_g depends only on incident pair indices. For a group set B, split B into nearly equal disjoint halves B1,B2. Condition on the directed-pair indices crossing B1/B2; recursively sum each side's internal indices and multiply. Ancestor-cut assignments are fixed parameters. Distributivity proves equality with the original finite mode sum. At singleton g, obtain Z_g through the actual prescribed child contraction; it is not a free oracle.

For each leaf l of this fixed balanced tree, let E_l be the union of cut-pair sets along its root-to-leaf path. The cut sets are disjoint. The number of paid calls is bounded by

    sum_l product_(e in E_l) |I_e|.

Sibling-internal domains contribute additive work, not a multiplicative factor to the cost of a particular leaf. Internal scalar loops add only a fixed polynomial factor to this paid-call bound. Pair indexing, accumulators and recursion stacks have polynomial bit size. The local tree depth is O(log r), and r belongs to a fixed finite set, so the overall network evaluation remains polynomial-space when both levels of recursion are traversed depth first.

## Exact cut profile and local coefficient

Let v(r) be the largest number of directed pairs along a balanced-tree leaf path:

    v(1)=0,
    v(r)=2 floor(r/2) ceil(r/2)+max(v(floor(r/2)),v(ceil(r/2))).

The path's root cut contributes the first term, proving the recurrence. For powers of two, v(r)=2(r^2-1)/3. The important counts are

    r:    3  4  5  6   8   13   14   15   16
    v(r): 6 10 18 24  42  118  132  154  170.

The per-directed-pair family envelope is `(2+o(1)) M/(r^2 D)`, and p<=(6+o(1))MD/u. Applying the joint slope-four weighted entropy estimate to each fixed path set gives

    log_2(paid calls) <= (kappa_stream(r)+o(1)) M/sqrt(u),
    kappa_stream(r)= (pi sqrt(2)/ln2) sqrt(v(r))/r.

This factor replaces the tuple-enumeration coefficient `pi sqrt(2(1-1/r))/ln2`; it must NOT be multiplied by the unequal-symbol fraction again. That fraction is already embodied by counting only directed pairs g!=h. Every selected path uses precisely such pairs.

## Generic schedule and sum

Use exactly the generic schedule already proved in `asym_schedule_new.md`:

    r_0,...,r_6 = 13,14,8,6,5,4,4,
    A_0,...,A_6 = 27/2000,21/800,333/10000,1933/50000,
                  861/20000,1183/25000,4999/100000,
    x_d=A_d-A_(d-1),
    r_(7+j)=3, x_(7+j)=(1301/400000)(3/4)^j.

Let m0=1, m_(d+1)=2m_d/r_d. Thus m7=1/5460. All established packing gates, uniform floor estimates, noncircular .7-shrink bootstrap, inherited precision and negligible entry-cost arguments remain valid verbatim. The new coefficient is

    sum_(d=0)^6 kappa_stream(r_d)m_d/sqrt(x_d)
      +kappa_stream(3)/[5460 sqrt(1301/400000)(1-4/(3sqrt(3)))].

Its seven prefix terms are

    46.096736154805, 7.166875998817, 1.359152262906,
    .392771526972, .150342149375, .056811051719, .035922052267.

The tail is .073010923617, unchanged because v(3)=3(3-1). Summing gives the displayed55.33162212048. The local call recurrence is multiplicative in the paid-call count, so its exponents sum exactly as before. Polynomial indexing/interpolation factors add only O(lambda log lambda) to the logarithm, and direct leaves remain lower order.

## Degree-.51 schedule and sum

Use `asym_schedule_lowdegree.md` unchanged, replacing only its local coefficient by kappa_stream:

    r=15,15,8,6,5,4,4,
    A=.0627,.11345,.1428,.162,.1771,.1911,.1999,
    r_tail=3, A_infty=.239, x7=.009775, tail ratio=.75,
    m7=1/6750.

The prefix terms are

    21.177502438879, 3.138551245934, .538824690477,
    .167865190438, .065571242212, .025378831296, .016005317912.

The tail is .034066458080. Their sum is25.16376541523. No naive scaling is used: the degree-.51 rounding/fresh-side guards remain those independently verified before the late packet arrived.

## Stronger combined comparisons

The late `subexponential_sat_frontier` prefix uses r=13,14,8,6 and x=[27/2000,51/4000,141/20000,107/20000], followed by r4 with x_(4+j)=(27/6400)(5/8)^j. Its streamed composition is55.40466590661057. The late `sat_frontier_improvements` prefix instead uses x=[27/2000,159/12500,71/10000,533/100000], with the same tail, giving55.409055136103966.

The checker certifies respective lower enclosures55.40455211252173 and55.40894169442198 using pi>314159/100000, ln2<693148/1000000, and one-sided integer-square-root bounds. Both exceed55.4, while our certified upper is below55.35. These are comparisons among explicit reported/composed certificates, not claims of global optimality over all contraction algorithms or all parameter choices.

## Exact evidence and replay

- `asym_schedule_checks/verify_streamed_composition.py`
- `asym_schedule_checks/streamed_composition_checks.json`
- Updated `asym_schedule_checks/verify_all_certificates.py`

The new checker independently enumerates balanced-tree path sets for r=1,...,64 and checks the recurrence and seven power-of-two identities. It checks every generic and degree-.51 packing gate, rational coefficient upper bounds, and the stronger late-comparison lower bounds. It uses explicit demand checks, not removable assertions; false constant and false path-profile controls are rejected in normal and optimized Python. No incoming code was run or imported. These are arithmetic/interface checks, not an end-to-end SAT solver or practical SAT timing claim.
