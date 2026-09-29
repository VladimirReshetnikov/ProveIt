# Proof audit

This is an internal mathematical audit accompanying the draft. It is not an
independent referee report or proof-assistant certificate.

## Core route

1. A computable null mask T gives G_T uniformly effective-dense equivalent
   to G. The forward procedure returns zero on T; the reverse procedure
   returns the explicit omission symbol on T. Both omission sets are null.
2. If G is 1-generic, a partial G_T-computable predictor cannot correctly
   predict G on infinitely many inputs in T. The c.e. set of bad finite
   predictions is avoided by a full cylinder. Flipping an unprotected
   deleted bit leaves the projected oracle unchanged and contradicts that
   avoidance cylinder.
3. Hence any effective-dense description d of G below G_T must omit all
   but finitely many elements of T.
4. For a null S below G, a least-missing-offset function f_S is total and
   G-computable. It is a genuine missing offset in every sufficiently late
   interval [m_n,2m_n); otherwise the density at 2m_n would be at least 1/2.
5. Computable agreement provides a total computable h agreeing with f_S
   infinitely often. Exactly one point m_n + h(n) mod m_n per interval
   defines a decidable null mask escaping S infinitely often. Its
   membership test waits only for a guaranteed total computation.
6. A proposed least representative g must be below G and compute a
   description d of G. The sparse mask escaping d's omissions gives
   g not below G_T, contradicting leastness. Candidates not below G are
   excluded by G itself. The witnesses remain binary and in the uniform
   class throughout.

## Existence and classical inputs

- A direct Sigma-2 meet-or-avoid argument proves computable agreement for
  every 2-generic. The exceptional partiality set has precisely the
  complexity needed: exists input, for all finite extensions and times,
  no convergence.
- Such generics exist below the second jump by a finite-extension
  construction, so the direct route has actual witnesses.
- The sharper low route invokes Kjos-Hanssen--Merkle--Stephan, Theorem 5.1:
  computing an eventually different function is equivalent to being high
  or of DNR degree. This is explicitly an external published theorem.
- The draft proves that 1-generics compute no DNR function, constructs a
  1-generic below the halting set, and proves its generalized-low jump
  calculation. Thus the constructed 1-generic is low and has computable
  agreement.

## Quantitative and structural extensions

- Every-prefix budgets are checked for N between consecutive block starts,
  not merely at endpoints. The lower bound m_n >= (n+1)Q_n guarantees a
  density bound even when the user budget itself is not sublinear.
- The ordinary-degree mask order is exactly reversed almost inclusion.
  Joins come from intersection. The full-degree meet theorem additionally
  uses a finite-amalgamation argument; it is not inferred from an order
  embedding alone.
- Countable simultaneous avoidance uses a *uniformly* G-computable family
  of descriptions. A finite-block selection of how many rows to include
  constructs a null upper bound without requiring convergence moduli.
  No statement about arbitrary countable coinitial families is inferred.
- The packed chain lists all total computable functions nonuniformly.
  Every individual mask is computable because it needs only a fixed finite
  prefix of this list. Fresh extra offsets ensure strictness even when
  consecutive functions agree. The union of all masks is null but is not
  computable from G; it cannot be substituted into the computable-mask lemma.
- A hypothetical in-class lower bound for the entire chain would yield
  an omission set covering every computable selector tail, hence an
  eventually different function below G. This proves the stated chain
  obstruction, not coinitiality or the nonexistence of all external lower
  bounds.

## Claims deliberately not made

There is no claim of no minimal elements in the full equivalence class,
no claim that arbitrary null changes preserve effective-dense equivalence,
no uniform algorithm for extracting masks from arbitrary oracle descriptions,
no effective enumeration of all total computable functions, and no machine
certification of the infinite mathematics. The numerical finite-check
counts are diagnostics, not statistical evidence for genericity or degree
inequalities.
