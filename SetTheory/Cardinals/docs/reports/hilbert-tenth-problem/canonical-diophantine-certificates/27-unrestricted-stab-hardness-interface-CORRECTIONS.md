# Printed defects and the mathematical reading used here

These are this review's mathematical corrections, not an author-issued erratum. The relevant expressions were checked in arXiv v2's PDF as well as HTML. Printed page numbers are used; the PDF index is one less. None of these corrections is a prerequisite for the new polynomial's independent raw physical equivalence. The hardness transfer can instead take the pinned Report35 loader as its explicit additional physical-simulation dependency.

## 1. Neighbor offset, §5.1, p.19

The printed pattern test is S_t(x)=π_k. It must test S_t(x+k)=π_k at each non-wildcard position k. The printed form compares every non-wildcard pattern entry to a single central state, so even an ordinary rule requiring two different neighboring symbols cannot match. The offset form is also the one implemented by the wiring at x+k in §5.2.1, p.20. This is a local indexing correction, not a new model choice.

## 2. Halting definition, §5.1, p.20

The definition uses “all but finitely many” lazy squares at some time. Read literally as a row property, this holds already at time zero for every intended finite initializer, including nonhalting computations. It cannot support the global-halting theorem.

Use instead a finite time H with every state equal to λ, and no earlier malfunction, as explicitly specified in Corollary 1, §5.2.3, p.21. For the particular finite-initialized, positive-input rule system in §6, an all-lazy row stays all-lazy. Finite propagation then makes this equivalent to finitely many active spacetime cells. The all-lazy and finite-support hypotheses are indispensable to the finite-total inference.

Do not apply the general wording of Lemma 4/Corollary 1 to arbitrary infinite initial activity or an arbitrary all-wildcard rule. Such variants can have activity not covered by the finite-initialized positive-input proof. The actual machine construction, and the pinned loader, meet the needed restrictions.

## 3. Endpoint and front placement, §6.2.5 and Figure 12, p.24

Let x0=min({−3}∪nonblank positions) and x1=max({3}∪nonblank positions), as defined there.

The printed right lazy cutoff uses x≥x0+2; its endpoint must be x1. More importantly, the figure places tape states at x0 and x1 with fronts immediately outside them, while the following prose places the fronts at x0 and x1. Both cannot be literal instructions when a boundary tape symbol is nonblank.

One consistent correction preserving Figure 12 is:

- Tape states on x0,…,x1, except for the headed state at zero
- Left front at x0−1 and right front at x1+1
- Lazy states at x≤x0−2 and x≥x1+2

This retains every nonblank input symbol and keeps the fronts outside the encoded tape. Alternatively choose fresh front coordinates L<R strictly outside the input support, put tape/head states on the open interval, and put lazy states outside [L,R]. Report35 uses exactly this second convention with L=min(−3,−|ell|−1) and R=max(3,|right|+1), so no ambiguous x0/x1 placement enters its initializer.

## 4. Shutdown delay, §6.2.6, p.25

The printed delay T±a+3 is not a general formula for variable front starting positions. With fronts initially at L and R and halt at (T,a), the correct two catching delays are T+a−L and T+R−a. Both fronts have disappeared by row H=T+max(T+a−L,T+R−a). The ±3 expression is the special case L=−3,R=3. This follows by solving the speed-two/speed-one intersection equations and agrees with the pinned loader's explicit H.

The source's qualitative eventual-catch argument survives; no time bound depending only on input size is inferred.

## 5. Initialization and partial activity are separate proof obligations

Section 5, p.19 explicitly rules out using the all-tape initializer from §3 for finite-total halting. Seeding finitely many wires is not enough if one such seed starts an infinite initialization wire. The global construction must directly initialize only a finite active interval and let the two moving fronts create further blanks.

The finite-output-gate assertion in §5.2.3 must also account for fired input wires and partly completed AND gates. Report35 §5 supplies the needed finite-neighborhood/diode argument. REVIEW.md §3 gives the detailed finite-set deduction from that contract. This is why the audit's strongest exact-interface route names Report35 as an additional dependency instead of silently filling every geometric/compositional gap in the published prose.
