# Decision, parity, sparse-test encoding, and black-box routes

Status: **No general worst-case asymptotic improvement has been proved here.** All consequences of the preprint are conditional on correctness of its tensor-contraction theorem. Source pin supplied by parent: `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`.

## Correct comparator

`main_full_version.tex:73–85` states deterministic exact counting in
`poly(n,m) 2^{O(n log log n / sqrt(log n))}`, and fixed-density
`poly(n,m) 2^{O_D(n / sqrt(log n))}`. The earlier `loglog^2` bound is explicitly called weaker at lines 87–94. None of the observations below is a claimed improvement over the stronger theorem.

## 1. Reducing root precision to parity does not change the proved contraction exponent

For the existing algorithm, a parent precision p is replaced by

`p_t = p + 8 ceil(3M/u) D_t + 8M(a+1)`.

See `quantitative-contraction.tex:250–268` (tapered Hermite recovery) and `:338–368`. Thus even p=1 leaves a positive term at least `24 M D_t/u`. The preprint proves the matching upper bound `p_t=O(M D_t/u)`. In its mode-count estimate `exp(O(sqrt(M p_t / D_t)))` this continues to yield `exp(O(M/sqrt(u)))`; see `:444–475`. This is a statement about what this algorithm and its certificate of running time establish, **not** a lower bound for every parity-counting algorithm. Randomized isolation might justify computing only parity, but cannot by itself delete the inherited interpolation precision.

With parity, the lift truncation can be taken as ell=1 and the local factor becomes `1+P_i` over F2. However the degree budget is still `K=k a=Theta(n)` when there are Theta(n) equations. Compare `quantitative-reduction.tex:153–177`, which uses `K=k(a+2(ell-1))`.

### Elementary degree obstruction for solution-preserving systems

Let `P_1,...,P_a` be polynomials over F2 on n Boolean variables. If
`sum_i deg(P_i)<n`, the number of their common zeros is even.

Proof: the indicator on the Boolean cube is `Q(x)=prod_i (1+P_i(x))` over F2, of degree less than n. For any monomial of degree below n, some variable is absent, and summing that monomial over the Boolean cube gives zero in F2. Therefore `sum_x Q(x)=0`, proving the claim. Consequently a same-variable, solution-set-preserving reduction that must handle a uniquely satisfiable instance cannot always have total polynomial degree o(n). In particular, degree-at-most-k tests need at least n/k equations in that case. This does not apply to arbitrary decision reductions or to reductions that deliberately change the set/number of witnesses.

## 2. The incidence support entropy can actually occur in solution-preserving parity tests from 3SAT

The following construction answers whether the generic sparse-equation example might be outside the SAT reduction's structural family.

In this construction logarithms are natural. Take any integer `n>=ceil(exp(10))`, and let `m=n ceil(log n)`. Choose m three-clauses on **distinct variable triples**, with arbitrary signs; there are at least m available triples at this threshold. There are enough triples. Write `v_e(x)` for the violation polynomial, so its cubic monomial is exactly the product of the variables of its triple and has coefficient one. Those cubic monomials are distinct across clauses, regardless of signs.

Choose `a=6n` rows independently. Include each clause in each row independently with probability

`theta = 4 log(2m)/n`,

which is less than 1/4 at the stated threshold (writing t=log n>=10, `theta<=8t exp(-t)<1/4`). Put `P_i=sum_{e in row i} v_e` over F2. Let `B=m/n` and `mu=m theta=4B log(2m)=Theta(log^2 n)`.

**Claim:** With positive probability, simultaneously:
1. the common zeros of the rows are exactly the satisfying assignments of the 3CNF;
2. every row contains between `mu/2` and `2mu` clauses.

Proof of (1): for a nonempty violation set of weight w, one row rejects with probability
`p_w=(1-(1-2theta)^w)/2 >= (1-exp(-2theta w))/2`.
If `2theta w<=1`, then `p_w>=theta w/2`. The probability this set escapes all 6n rows is at most `exp(-3n theta w)=(2m)^(-12w)`. Union bound over at most `m^w` sets, followed by summation over w>=1, is at most `r/(1-r)`, where `r=2^(-12)m^(-11)`, hence less than `1/4095`. If `2theta w>1`, then `p_w>1/4`; a union bound over the `2^n` assignments bounds this failure probability by `[2(3/4)^6]^n<1/4` at the stated threshold. Every satisfying assignment passes automatically.

Proof of (2): a row size is Binomial(m,theta), with mean mu. Chernoff bounds give failure at most `exp(-mu/8)+exp(-mu/3)` per row, hence total at most `6n[exp(-mu/8)+exp(-mu/3)] <=12 exp(t-t^2/2)<=12 exp(-40)<1/4`, where t=log n>=10; here `mu>=4t^2`. Thus all properties hold together for some matrix.

Every such row is a degree-three polynomial with `O(log^2 n)` listed clause terms (and at most eight times as many ordinary monomials), and has at least `mu/2` distinct cubic monomials. Its scope is at most `6mu=O(log^2 n)`. If each test-variable incidence is given a separate indeterminate, as in `quantitative-reduction.tex:161–168`, then

`F(z)=prod_{i=1}^{6n} (1+P_i(z_i))`

contains at least `(mu/2)^(6n)=2^{Omega(n log log n)}` distinct nonzero incidence monomials: choose one of the distinct cubic monomials in each factor; the indeterminate sets of different factors are disjoint, so the product choices cannot coincide or cancel. The full support is at most `2^{O(n log log n)}` as well, because each factor has only polylogarithmically many terms. Thus its support entropy is Theta(n loglog n).

The preprint's degree-array enumeration has at most `2^{O(sqrt(n) log n)}` arrays (`quantitative-reduction.tex:202–218`). Therefore at least one array contains `2^{Omega(n loglog n)}` of these monomials. Any injective binary monomial-index representation within that array requires Omega(n loglog n) bits. This explains why merely tightening the stars-and-bars estimate (`:224–239`) cannot generically remove the loglog factor, even for legitimate solution-preserving 3SAT parity systems.

**Scope of the barrier:** This is NOT a SAT lower bound, not a proof that the deterministic greedy reducer must choose these matrices, and not a proof against a different representation. Identifying all incidence copies of each original variable can create enormous cancellations and reduce the support to at most `2^n`. A method that performs that quotient implicitly, while retaining cheap local evaluation and low tensor degree, would evade this barrier. The existing proof has not supplied such a method.

## 3. Optimizing ordinary sparsification plus the fixed-density counter is insufficient

The occurrence certificate is
`B=O_k((sigma^{-1} log(2/sigma))^{k-1})`
from `main_full_version.tex:3543–3565`. Using clause networks directly on every leaf gives the upper-bound exponent

`O_k(n [sigma + sigma^{-(k-1)} log^{k-1}(2/sigma)/sqrt(log n)])`

for inverse-polylogarithmic sigma, since `log(Bn)=Theta(log n)` in this regime. Optimizing this displayed certificate yields

`sigma ~ (log n)^(-1/(2k)) (loglog n)^((k-1)/k)`.

For k=3 this is

`2^{O(n (loglog n)^(2/3)/(log n)^(1/6))}`,

which is asymptotically worse than the strongest preprint exponent by a factor `Theta((log n/loglog n)^(1/3))`. This does not rule out stronger sparsification results; it only rules out presenting a retuning of this guarantee as an improvement.

## 4. Exhaustive variable restrictions do not bootstrap the stated bound

If a black-box call on N variables is charged `2^{C f(N)}`, where
`f(N)=N loglog N/sqrt(log N)`, branching on t variables is charged
`2^{t+C f(n-t)}`. For large n, the derivative `f'(N)` tends to zero. For `t<=n/2`, the derivative of `t+C f(n-t)` is positive, so the certificate is minimized at t=0. For `t>n/2`, the branching charge is at least n/2, whereas `C f(n)=o(n)`. Thus exhaustive restrictions followed by the same black box yield no smaller asymptotic guaranteed exponent. This is only a restriction on that black-box strategy.

## 5. Exact conditional compression criterion (a research target, not an established reduction)

Assume the preprint's Boolean tensor contraction theorem. Fix a function W(n) with `n<=W(n)<=n(log n)^c` for fixed c. Suppose there is a deterministic, polynomial-space streaming procedure which, for every kCNF F on n variables and m clauses, constructs at most

`poly(n,m) 2^{O(W(n)/sqrt(log W(n)))}`

bipartite Boolean tensor networks, in the same total time, with the following uniform fixed-constant guarantees:

* every network has at most C W(n) wires and at most a fixed polynomial in W(n) vertices;
* maximum degree at most `ceil(W(n)^(9/10))`;
* entries lie in `(Z/2^(n+1)Z)[V]/(V^ell)`, with `1<=ell<=C W(n)`;
* let `Ldesc` be the total graph-plus-evaluator description length, bounded by a fixed polynomial in the encoded input length; the immutable description may include the original input encoding without adding wires;
* each entry, at any Boolean port assignment, is computed in `(W(n)+Ldesc)^b 2^{A W(n)^(9/10)}` time and `(W(n)+Ldesc)^b` space, with fixed A,b independent of F and n;
* after a specified polynomial-time linear functional on the ring, the sum of all contractions equals `#F mod 2^(n+1)`.

Then exact counting, and hence decision, takes

`poly(n,m) 2^{O(W(n)/sqrt(log W(n)))}`

and polynomial space. Proof: apply the contraction theorem with s=W(n), stream the calls and add their answers modulo 2^(n+1). The number of calls multiplies the per-call time but adds only another constant to the exponent. The count is between zero and 2^n, so its residue is exact. Store one network and accumulator at a time.

In particular W(n)=O(n) gives the genuine stronger target
`poly(n,m) 2^{O(n/sqrt(log n))}` for arbitrary density. Any `W(n)=o(n loglog n)` would already give a strict asymptotic improvement over the preprint's general bound. **The missing theorem is this compression, not the final application of the contraction theorem.** Merely saying that there are only n original variables is insufficient: representing all factors by one arbitrary-degree n tensor violates the theorem's maximum-degree hypothesis, and splitting it without controlling wire count or entry-evaluation cost is exactly the unresolved work.

## 6. A more structural possible escape: recurse before incidence expansion

The older original-variable interface in `main_full_version.tex`, from `sec:counting` through equations `general-product-degree`, `general-count-polynomial`, and `three-costs`, already sums over only n Boolean variables and has total input degree O(n), despite polylogarithmic factor scopes. Its global Taylor/measurement bound is weaker, with loglog^2 overhead.

A recursive, tapered-precision analogue that closes on this interface could potentially avoid the nloglog incidence code. Required proofs include: (i) transformed group factors retain product degree O(number of local variables), (ii) shared measurement and correction variables do not reintroduce an nloglog bit budget, (iii) local coefficient/evaluation procedures meet the subdominant time bound with polynomial space, (iv) precision growth and interpolation denominators remain controlled at every depth. None of these closure properties follows just by invoking Appendix D. This is an unproved proposal, not an algorithm or claimed runtime.

## 7. A decision-only obstruction to sampling a small subformula

For each N>=2, use primary variables x_1,...,x_N and include every pair clause `(not x_i or not x_j)`, i<j. Add a linear-size 3CNF circuit encoding that at least two primary variables are true:

* let s_1 be x_1, and introduce t_1 with the unit clause not t_1;
* for i=2,...,N, introduce `a_i=s_{i-1} AND x_i`, `s_i=s_{i-1} OR x_i`, and `t_i=t_{i-1} OR a_i`;
* assert t_N with a unit clause.

Use the usual exact three-clause encoding of each AND/OR gate (each gate output is uniquely determined by its inputs). There are `n=4N-2` declared variables and O(N) gate clauses, in addition to the binom(N,2) pair clauses. The full formula is unsatisfiable: the pair clauses force at most one true primary variable and the circuit forces at least two.

For every pair {i,j}, deleting its pair clause makes the formula satisfiable: set exactly x_i=x_j=1, all other primary variables zero, and use the uniquely determined circuit values. Thus **every unsatisfiable subformula must contain all binom(N,2)=Omega(n^2) pair clauses**. Any subformula omitting one pair is satisfied by that witness, even if it retains every circuit clause. This rules out retaining O(n), or even n polylog n, original clauses as a universally correct decision sparsifier. Clauses of width one and two can be padded by repeating literals if exact width three is required. It says nothing against branching, newly derived constraints, or parity-test compression.

## 8. Random extension-field hashing and the norm idea: exact benefit and missing oracle

Let q=2^b with b>=n+2, choose independent uniform coefficients a_e in F_q, and put `P(x)=sum_e a_e v_e(x)`, where v_e is the Boolean clause-violation polynomial of degree at most three. For any fixed nonsatisfying assignment, at least one violation is one, so P(x) is uniform in F_q and vanishes with probability 1/q. A union bound gives probability at most `2^n/q<=1/4` that any nonsatisfying assignment survives. Satisfying assignments always map to zero. This is a valid randomized same-variable compression to **one** extension-field equation.

For Boolean inputs, the norm identity is

`1_{P(x)=0}=1+P(x)^(q-1)=1+prod_{r=0}^{b-1} Q_r(x)`,

where `Q_r(x)=sum_e a_e^(2^r) v_e(x)`. Indeed v_e(x) is in F2, so it is fixed by Frobenius on the Boolean cube; Q_r has degree at most three. The product has degree at most 3b=O(n), and its Boolean multilinear representative uses only n indeterminates, unlike the disjoint-incidence expansion.

This does **not** yet give an application of the tensor theorem:

1. With one global factor, the coefficient oracle for a selected set S is the Boolean Möbius sum of 2^|S| evaluations. In characteristic two all signs are plus. For S=[n], this is 2^n evaluations; the source's generic coefficient procedure therefore does not meet the `2^{O(s^{9/10})}` entry bound with s=O(n). No faster structured-norm coefficient algorithm is proved here.
2. A single tensor indexed by n subset bits has degree n, violating the maximum-degree bound `ceil(s^{9/10})` when s=Theta(n). A decomposition must also bound all new wires, not merely tensor-description size.
3. Splitting into the b Frobenius-conjugate factors recreates up to bn=Theta(n^2) incidences. With degree budget K=Theta(n), the generic support-index budget becomes O(n log n), worse than the source's nloglog bound. This is an upper-bound limitation, not a universal lower bound for the special conjugate structure.
4. Grouping g conjugates reduces the number of factors but does not immediately fix the problem. The straightforward local coefficient oracle uses up to `2^{3g}` evaluations. Keeping g below the existing `n^{9/10}` scale leaves `log(n/g)=Omega(log n)` in the generic subset-encoding estimate. More sophisticated factorization could evade this observation but requires proof.
5. The hash is randomized. The displayed norm polynomial lives in characteristic two, so summing it directly supplies only count parity, not the integer count modulo 2^(n+1). An exact-counting route would additionally need a justified lift with controlled degree and precision. Deterministically selecting its field coefficients, and using a parity-valued result to decide existence rather than only count modulo two, are additional tasks. A norm identity alone does not solve either. Randomized isolation could address the latter with extra constraints/overhead, not the missing coefficient oracle.

A fast, low-wire, low-degree representation of this Frobenius-structured norm would be a substantive new theorem and could be a valid path to an improved algorithm. It is not established by the identity or by the current contraction theorem.
