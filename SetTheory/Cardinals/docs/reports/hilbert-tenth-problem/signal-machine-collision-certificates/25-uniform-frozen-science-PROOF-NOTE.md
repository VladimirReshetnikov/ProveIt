# Uniform four-mass charts: proof note

4 October 2026. Conditional mathematical proof; independent scoped structural review: PASS. This is a mathematical extension of the pinned source-17 section construction and source-18 fixed-input charts, not a new CA construction, an implemented general compiler, or a literature-priority claim. No upstream executable or saved schedule is used.

## 1. Exact statement and arithmetic syntax

Fix a one-dimensional finite-radius CA F with finite alphabet, a unique weight-zero vacuum, positive integer weights on nonzero states, conservation on finite supports, and at most one weight-one symbol. Fix an input label tuple a=(a_1,...,a_m) of total mass at most four, with external signed coordinates x_1<...<x_m. If a unit exists, let G=tau_{-delta} F fix its isolated unit; otherwise put G=F, delta=0, and S=max(1,R).

The theorem proved here has the following explicit syntax:

* There is one finite effective family for the fixed rule and input label tuple, uniform in all x.
* The input space has a finite disjoint partition into cells given by integer-affine inequalities/equalities and fixed-modulus congruences in the initial gaps g_i=x_{i+1}-x_i. These are Presburger input cells, not literally polyhedral cells in the raw x alone.
* Over such cells, each chart has at most two additional natural evolution parameters. Its remaining domain conditions are rational-affine inequalities/equalities in x and those parameters, with denominators cleared positively. The output labels are fixed. Its time is a rational polynomial of total degree at most two; its stationary-frame occupied coordinates are rational-affine. All outputs are integral on their domains.
* For every valid x, the disjoint union of chart domains maps bijectively to the full timed orbit (time plus strictly sorted labeled support).

There is a literal affine-domain version, with the cost stated rather than hidden. Choose a single fixed positive modulus H resolving every input congruence used by the finite construction. Split by gap residues 0<=r_i<H, and add the uniquely determined natural input coordinates u_i through

    x_{i+1}-x_i = H u_i+r_i  (1<=i<m).

The ordered-input guard makes u_i natural (and enforces u_i>=1 if r_i=0). On this lift all domains are integer-affine, with at most (m-1)+2<=5 natural parameters. Only two are free evolution parameters; the other m-1 are canonical input-dependent quotients. No claim of two total natural auxiliaries for literal affine domains over unrestricted raw x is made. For m=0 the vacuum has its usual one-clock chart.

Consequences: uniform stationary-frame untimed configuration reachability is Presburger; original-frame time and positions are quadratic after adding delta times time; and the source-18 compiler supplies a fixed-rule/input-and-output-label-case finite-arity natural-single-fold quartic for the uniform timed relation, with the input-quotient witnesses included in its ledger. Alternatively, finitely many output-label cases may use one tagged, padded output encoding.

## 2. Imported finite data, and exactly what is new

The pinned article is ../four-particle-clock-independent-audit-20261004/inherited-article-source.tex, SHA-256 17d3c0d9b449c689f88c1dc082ffee9b116993e4f5585b65d52c4fe591b2d962.

Source 17, lines 5979-6340, supplies:

1. The stationary-unit frame of radius S and exact independence of components separated by more than 2S.
2. A finite library of connected mass-two packets, each with an eventually translated-periodic isolated orbit, and connected mass-three seeds, each with a finite prefix leading to a compact finite-phase outcome or an emitted packet plus stationary marker.
3. Fixed thresholds B,N,W, with ordinary four-mass states of diameter at most W, and safe isolated resolution of a distant seed plus the fourth unit.
4. Live sections with two markers L<R, D=R-L>N, and a mass-two head launched toward the other marker. Refined by a fixed gap residue, each continuing live edge has D'=D+c, L'=L+e and duration alpha D+beta, with finite phase descriptions of every intermediate time. Noncontinuing compact outcomes either escape or reach an ordinary state after one affine-phase flight.
5. Effective complete fixed-input normal forms. Source 18, lines 6660-6797, makes these disjoint half-open charts with at most two evolution parameters, quadratic time and affine stationary-frame positions.

We do not re-prove those dynamical ingredients. The additional work is parameter-uniform initial dispatch, a fully guarded symbolic contracting-cycle acceleration, and composition at the first ordinary reset without materializing an input-dependent prehistory.

Crucial simplification: only the initial live excursion can retain arbitrary input gaps. At the first ordinary reset, its normalized complete configuration belongs to a fixed finite set; its later orbit is a translate and time shift of one precompiled fixed-input template. There is no need to symbolically concatenate an unbounded number of input-dependent excursions.

## 3. Uniform first-contact lemma

Consider finitely many fixed finite-phase objects with independent counterfactual motion and anchors affine in x. After a common fixed transient and common fixed phase period P, in phase r every occupied site has form

    a_v(x)+b_{v,r}+d_{v,r} k,    time = mu+r+P k, k>=0,

where every d_{v,r} is a fixed integer. The objects involved below are mass-two packets, compact mass-three library outcomes, and stationary units. For contact of a fixed occupied site pair, the condition is

    -2S <= A(x)+d k <= 2S,

where d is fixed. This exact site-pair criterion avoids a hull assumption for compact mass-three shapes with holes. A finite union covers all pairs whose interaction is being monitored.

If d=0, that phase either has no candidate or its earliest candidate is k=0, according to affine conditions on x. If d>0, its earliest possible k is

    max(0, ceil((-2S-A(x))/d)),

and this candidate is retained only if the upper inequality holds; d<0 is handled by reversing signs. Refine the relevant numerator modulo |d|. Then each ceil is rational-affine, and the max is handled by two disjoint affine cases. Every finite-transient candidate has constant time and affine eligibility conditions.

Select the earliest among the finitely many valid candidates, breaking candidate ties by a fixed index. All comparisons are affine after residue refinement. Thus there is a finite disjoint input partition on which either no contact ever occurs, or the first contact time h(x) and all contact positions are affine. Candidate ties only choose an arithmetic description; the actual contact configuration includes all simultaneous contacts.

Every precontact time is represented canonically by transient-time charts and phase charts with

    0<=mu+r+P k<h(x),

or with no upper bound in a no-contact cell. Their support coordinates are affine. At the first contact time, actual and counterfactual configurations still agree and have disjoint supports: the preceding components were farther than 2S apart, so independence and disjoint outputs hold for that preceding step. The contact time is assigned to the next piece.

All normalized bounded encounter shapes can be selected by finite affine equalities and ordering cases. The first-contact lemma remains valid if the anchors and entry time are already affine functions of x. Every division is by a fixed rule-dependent nonzero integer; there is no variable divisor.

## 4. Uniform initial dispatch

Partition initial coordinates by 2S-component structure, internal bounded gaps and labels. A connected component of mass b has diameter at most 2S(b-1), so its normalized shape comes from a fixed finite list. All partition tests are affine.

For mass four the possibilities are:

* 4: the configuration is ordinary (diameter <=6S<W).
* 1+1+1+1: stationary under G.
* 2+2: apply the first-contact lemma to the two packet profiles. No contact gives a synchronized independent terminal profile. First contact has diameter <=6S<W and is ordinary.
* 3+1: if not already ordinary, use the safe seed library. Its finite prefix has fixed length. An emitted head gives an outward terminal independent profile or a live section; a compact outcome either stays independent or first contacts the fourth unit in an ordinary configuration. Its possibly arbitrarily long compact flight is handled by the first-contact lemma, not declared constant-time.
* 2+1+1: apply the first-contact lemma to the packet and both units, choosing the actual earliest time and retaining simultaneous contacts. Simultaneous contact connects all four masses and has diameter <=6S. Otherwise the contacted three-mass seed plus remaining unit is either ordinary or safely distant; apply the previous seed case.

At a designated inward emission checkpoint apply the source-17 live-tag convention when D>N; otherwise use the specified ordinary/terminal dispatch. Since every necessary threshold test uses affine positions, the representation choice is uniform and affine after residue refinement.

Each initial path contains only a uniformly bounded number of symbolic stages: at most one first packet contact, one fixed seed prefix, and (if compact) one compact flight. It ends in an independent terminal profile, an ordinary state, or a live section. On every disjoint input cell the entry time, anchor and live gap are affine in x. Every intervening time already has a half-open affine-domain chart with at most one evolution parameter and affine time/support.

For total mass <=3, the same argument with the finite mass-three core (source 16) gives initial affine first entry plus finitely many fixed core templates. These cases need only affine timed outputs.

With no unit symbol, every occupied site has weight at least two, so there are at most two occupied sites. If there are two separated sites, both have weight two. An isolated weight-two site must evolve to exactly one weight-two site; its label has finite-state motion and hence an eventually translated-periodic profile. Use all configurations of diameter <=2S (including singletons) as the finite normalized core. Outside it, two sites follow their independent finite-phase profiles until first proximity <=2S. The first-contact lemma is affine uniformly in the initial gap. From a normalized core state, take one step and accelerate to the next core return or an independent terminal tail. This is a finite deterministic graph with fixed time and translation increments on its edges; repetition gives a fixed translated-periodic template, and escape gives a fixed independent template. Thus these cases also have uniform affine timed charts. No stationary-frame shift or unit assumption is used in this paragraph.

## 5. Finite control and guarded cycle acceleration

Absorb D modulo a common fixed modulus into the live control q. Enlarge the modulus to include every denominator and compact-outcome contact residue used in noncontinuing edges. For each q there is one large-gap continuation itinerary, until a small-gap guard fails or a noncontinuing outcome is reached. Its continuing edge updates are fixed constants

    D -> D+c_q,    L -> L+e_q,    duration = alpha_q D+beta_q.

The source-17 construction makes these formulas valid for all current live gaps D>N. Continuing to the next live state additionally requires the next gap >N. All local flight and scattering phases are retained.

Follow the finite control for at most |Q| edges. Before the first repeated control, every duration and position is affine in the initial live D,L. Each possible early failed continuation guard, terminal outcome or compact ordinary reset is a finite affine branch; the latter's extra contact flight uses Section 3. If a control repeats, its intervening word is a fixed cycle with m edges.

For that cycle define

    c_0=0, c_s=sum_{i<s} c_i(edge), c_m=Delta,
    e_0=0, e_s=sum_{i<s} e_i(edge), e_m=E,
    b=min_{0<=s<=m} c_s.

Let d,l be gap and left marker at cycle entry. At cycle n, phase-edge s starts with

    D_{n,s}=d+n Delta+c_s,
    L_{n,s}=l+n E+e_s.

A whole cycle is completed live-to-live iff every endpoint guard holds:

    d+n Delta+c_s>N for s=0,...,m.

It is essential to include s=m and every interior endpoint, not merely the cycle-start guard.

If Delta>=0 and d+b>N, every later cycle is valid. This includes Delta=0: its physical period may depend on d, so one must retain cycle/flight charts rather than enumerate a purported fixed period uniform in the input. If d+b<=N, the first cycle fails; the first failing endpoint is selected by finitely many affine inequalities and gives an ordinary reset.

If Delta=-a<0, the exact number K of wholly completed live-to-live cycles before the failing cycle is

    K=max(0, ceil((d+b-N)/a)).

Indeed cycle n is completed exactly when a n<d+b-N. This gives the displayed count, including the case K=0. After K completed cycles the start is still live (the previous final endpoint guard was included), and the next cycle has a first failed endpoint s in {1,...,m}. Select s by

    d-Ka+c_r>N for 0<=r<s,
    d-Ka+c_s<=N.

The edge from s-1 is actually traversed; its final emission belongs to the ordinary state. The partial cycle owns all times strictly before this reset.

Refine d+b-N modulo a and the sign cell. K becomes affine in x. No extra free cycle-count variable survives in the reset data. The failed endpoint's gap is bounded: the preceding gap exceeded N and the fixed last decrement crossed N. Therefore its complete launch configuration is one of finitely many normalized ordinary shapes. Selecting the shape is a finite affine case split. Its anchor is affine in x because it is l+K E plus fixed edge offsets.

## 6. Quadratic clocks, with all phases

Write the duration of edge i at gap z as alpha_i z+beta_i. Let

    A=sum_i alpha_i, B=sum_i(alpha_i c_i+beta_i),
    A_s=sum_{i<s} alpha_i,
    B_s=sum_{i<s}(alpha_i c_i+beta_i).

A full cycle entered at gap z lasts A z+B. If its initial global time is T_*, then the start time of edge s in cycle n is

    S_s(n)=T_*+n(A d+B)+A Delta n(n-1)/2
                  +A_s(d+n Delta)+B_s.

The initial dispatch and finite control preperiod make T_*,d,l affine in x. Thus S_s has total degree <=2 jointly in x,n, including the necessary cross term n d. No coefficient depending on x multiplies n^2.

For a flight of fixed packet period p, refine its phase r and use n,j>=0 with

    time = S_s(n)+r+p j,
    0<=r+p j<h_s(d+n Delta),

where h_s is affine (constant edge offsets are absorbed). Positions are affine in x,n,j. A fixed local-prefix phase v has time S_s(n)+h_s(d+n Delta)+v and positions affine in x,n. Flights/short prefixes own half-open consecutive intervals; their endpoint launches belong to the next piece.

For a contracting cycle use 0<=n<K(x) for completed cycles. This is an affine domain bound. On the last partial cycle substitute n=K(x), select its first failing endpoint as above, include every whole edge before it and every phase of the failing edge strictly before its endpoint. Only j remains free in these partial-cycle charts; time is quadratic in x,j (indeed affine in j), and support is affine. For a failing first cycle use K=0. For nonnegative cycles with valid first cycle use n>=0 with no upper bound.

The reset timestamp is S_s(K), i.e. the start time of the first non-live endpoint. It is quadratic in x. Positivity of actual edge durations and Euclidean division within each packet period give unique ownership of every pre-reset time. Strict sorting of occupied sites is an affine refinement because stationary-frame differences are affine.

## 7. First reset composition, completeness, and consequences

For every normalized ordinary state o (diameter <=W), precompute once the source-18 complete fixed-input chart family starting from o. There are finitely many such states. A cell reaching its first ordinary state at time Q(x) and anchor a(x) has Q quadratic and a affine. For a fixed template chart (t_o(z),v_o(z)), substitute

    time = Q(x)+t_o(z),
    stationary position = a(x)+v_o(z).

The template has <=2 natural evolution parameters, affine domain, quadratic t_o and affine v_o. Consequently the shifted chart retains those degree bounds. This is addition, not composition of a quadratic function into another quadratic argument. Its earliest time is exactly Q(x), and the pre-reset charts stop strictly before Q(x).

There is no need to retain the initial contraction count as another witness or to analyze later resets symbolically. The complete normalized reset shape erases every unbounded control coordinate except the translated anchor. Any enormous prehistory of its fixed template depends on the rule and normalized ordinary state only, so materializing it does not violate input uniformity.

Together the initial-dispatch pieces, nonreset live pieces and first-reset templates cover the entire orbit. Their deterministic input partition, first-contact tie-breaking, first failing endpoint, half-open stage ownership, cycle count and Euclidean phase quotient prove bijectivity for each x. Sorting adds the unique permutation of distinct occupied sites, with labels transported accordingly.

All input residue refinements are finite and divide only by fixed constants. They depend on relative coordinates, hence on initial gaps, not the overall anchor. After the finite symbolic construction, first pull every residue test back to an integer-affine congruence in the initial gaps. Concretely, if an integer-valued affine expression (a dot g+c)/d is to equal rho modulo M, use a dot g+c = d rho modulo dM on its existing integrality cell. Choose H as a common multiple of these pulled-back moduli dM. Taking merely the least common multiple of d and M separately would be insufficient (for example, (D/2) modulo 2 requires D modulo 4). The canonical quotient lift in Section 1 then gives literal integer-affine domains. Each chosen raw input determines exactly one residue vector and exactly one u vector, so it does not introduce duplicate witnesses.

Dropping time from the stationary-frame charts leaves only affine outputs, affine domains and fixed input congruences. Existentially quantifying their natural parameters therefore gives a uniform Presburger relation for complete output configurations, with output labels selected from a fixed finite list. Translation queries and any fixed finite-pattern observation, including zero requirements, are further Presburger constructions. This is an untimed claim; time itself remains quadratic and need not be Presburger.

Original-frame positions equal stationary positions+delta*time and have degree <=2. A uniform quartic requires one extra compiler precaution. The source-18 constant-term lift cannot be applied directly to a polynomial f(x,z) with quadratic external-input terms: multiplying f(x,0) by a selector could raise degree to three. Instead encode each external initial x_i by its canonical natural pair x_i^+,x_i^-, and introduce, for every chart h, private natural copies X_hi^+,X_hi^- with residuals

    X_hi^+ - e_h x_i^+ = 0,    X_hi^- - e_h x_i^- = 0.

These are quadratic. Include all copies in that chart's inactive-zero gate. Use X_hi^+-X_hi^- everywhere that chart used x_i, so its affine domain and quadratic outputs now involve only private natural variables. The source-18 constant-term lift then applies unchanged to those forms. On the selected chart the copies equal the fixed external input; on all inactive charts they vanish. Hence the copies are uniquely determined and introduce no duplicate witnesses. Count up to 2m input-copy variables per chart in addition to the m-1 quotient variables, at most two evolution variables, selectors and inequality slacks. The per-chart private-variable bound before slacks is 3m+1<=13, not two. An overall fixed-rule arity follows; no optimized numerical ledger is claimed.

All residuals now have degree <=2, so their squared sum has degree <=4. On valid canonical input coordinates the natural zero fiber is empty or a singleton for each external timed configuration. If a polynomial is required to reject noncanonical external coordinate pairs as well, append the quadratic residual x_i^+ x_i^-=0 (squared in the final polynomial) for each input coordinate. Output-coordinate canonicality can be handled the same way. This extension preserves degree four.

## 8. Scope and remaining checks

This note is conditional on the imported source-17 finite section mechanism and source-18 fixed-input chart theorem, both pinned above. It is intended to supply the missing uniform extension rather than re-prove those hypotheses. The literal two-total-parameter affine-domain claim over raw input coordinates is not asserted. The claimed uniform extension uses transparent input congruence cells, equivalently at most three canonical input quotients plus two evolution variables.

Independent structural review in REVIEW.md returns PASS for the stated residue-cell/quotient-lift theorem, conditional on the imported source-17/source-18 results. The fresh self-contained arithmetic checker passes 26,733 first-contact interval cases; 69,800 direct contracting-cycle comparisons over 1,396 different words; 105 contracting tests at gaps through 10^100; 1,538 nonnegative-cycle guard cases; and 225 quadratic-substitution directional checks. These checks validate arithmetic fixtures, not the all-rules theorem or a CA compiler. No external published-priority claim is made.
