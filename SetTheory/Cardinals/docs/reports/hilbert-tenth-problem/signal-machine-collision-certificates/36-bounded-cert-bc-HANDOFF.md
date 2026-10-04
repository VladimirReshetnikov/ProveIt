# Separate candidate ready for independent review

The three-witness proposal is sound. The sharp uniform shifted clipping threshold is K=T+1, not the unnecessary K=T+2: before transition t+1 with t<T, a clipped native tail is at least T-t>0. It may reach zero after transition T, which does not affect the first T branches or q_T.

## Main proof checks

- `PROOF.md`, Section 2: clipping proof, zero horizon, initial halt, loops, and a counterexample to the smaller uniform threshold
- Sections 3-4: finite acceptance tables and the explicit integer Lagrange coefficients with d=(N-1)!
- Section 5: six residuals, exact clipping by positivity, unique triple, and the degree-two T=0 polynomial
- Section 6: joint degree bound and the explicit coefficient norm bound 66L^4, L=K 2^(N-1)(N+1)!
- Section 6.1: proved support ceiling 16N-5, O(N^2 log(N+1))-bit expanded description, and explicit arithmetic-operation versus horizon costs
- Section 7: fixed-arity family versus one fixed polynomial with unbounded horizon
- Section 8: all paid POWER equations, 57 witnesses, 38 listed residuals, and the loss of full-witness uniqueness

## Resource accounting

For T>=1 the native polynomial has three positive witnesses, two positive inputs, six listed residuals, one equation, and degree at most 4(T+1)^2-4. The first-exact-halt variant has the same counts. At T=0 it still has three positive witnesses and six listed residual slots, but two products vanish identically and the polynomial degree is two.

The native-gap composition has 57 positive witnesses, three positive inputs, 38 listed residuals, and degree max(12,deg P). Do not count the two power outputs twice. Do not assert unique or finite full witnesses: a paired congruence quotient gives infinitely many tuples.

The degree ceiling is intentionally not claimed to be exact. For example the fresh algebra check gives degree 28 at T=2, below the ceiling 32; at T=4 it gives 92, below 96. No artificial degree padding is used.

## Evidence and dependencies

The fresh inspected checker passed 140 interpolation nodes, 28 arbitrary-table ledgers, 1,904 input-grid uniqueness checks, 73,600 literal witness triples, nine declared fixtures, and 18 complete native-gap ledgers. No counter interpreter or physical simulation was executed. The table-generation algorithm is defined mathematically only.

The main three-witness theorem uses no Pell or physical dependency. The native-gap composition imports the pinned constructive Pell theorem pair and positive-domain module from the retained native-gap proof. Its physical interpretation separately imports the retained five-signal compiler theorem. Those dependencies are not conflated with finite check results.

This is an unnumbered local proof candidate, not a claim of delivered report numbering. It does not modify either prior source directory. No novelty, priority, minimality, or exhaustive literature-search claim is made.
