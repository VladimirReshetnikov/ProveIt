# Proof audit and evidence boundaries

This is a record of obligations rechecked while preparing the draft. It is not
an independent referee report, a proof-assistant certificate, or an assertion of
bibliographic novelty.

## 1. The topology is not the zero pseudometric

Inside C_X, the upper asymptotic density discrepancy delta is identically zero.
The proofs instead use d(U,V) = sup_n |(U triangle V) intersect [0,n)| / n.
This is a genuine metric controlling every coordinate. Completeness is proved
by coordinate stabilization of a d-Cauchy sequence and an explicit estimate
showing its limit still differs from X on density zero. Finite modifications
of any one description are d-dense. Late single-bit changes show there are no
isolated points.

The separability assertion concerns C_X, not the entire ambient binary space
under d. No unjustified global separability assumption is used.

## 2. The local recovery algorithm is an actual oracle procedure

Its only fixed parameters are an oracle-program index e and a positive rational
radius r. It enumerates finite sets F with norm(F) < r/2, an effectively
decidable condition, and dovetails computations with oracle C triangle F.

The center Z, the target A, and the dense fiber are used in the proof but are
not supplied as hidden oracles. Correctness takes any finite halting computation,
splices its prefix to the tail of Z, and uses density to find a true fiber member
with that same computation. The radii are:

- d(C,Z) < r/4;
- norm(F) < r/2;
- d(C triangle F,Z) < 3r/4 < r.

Termination uses a fiber member W inside the r/4 ball. Its finite computation
has an error set F with norm(F) <= d(W,C) < r/2. Thus at least one eligible
simulation halts. No search for membership in a dense fiber is performed.

## 3. Strict supremum bounds are maintained

An eventual assertion that all prefix ratios are strictly below r/4 need not,
by itself, make their supremum strictly below r/4. The compactness proof chooses
an intermediate rational q below r/4 and obtains a supremum at most q. This is
why the correction oracle satisfies the strict hypothesis of local recovery.

## 4. Meagerness and simultaneous avoidance

If A is not in K_X, choose a genuine coarse description D_0 not computing A.
Were one computation fiber somewhere dense, a finite modification of D_0 could
be put in the recovery neighborhood. Recovery would contradict finite-change
invariance of Turing degree.

For countable avoidance the construction avoids the *closures* of the fibers.
Their complements are open dense, so the resulting set is a dense G-delta.
The desired collection of exact partners is said to contain a dense G-delta;
it is not asserted to itself be G-delta.

The set of all sets computable from a fixed oracle Y is countable. Its members
outside K_X need not be effectively enumerable. No step treats abstract
countability as computable enumerability.

## 5. The c.e. example and its jump degree

The definition waits for all inputs i <= n of the relevant program to converge
with binary outputs, and then requires output zero at n. This is a finite
positive witness, so it yields a c.e. set without deciding totality.

A non-total or nonbinary program has a least bad input. Its column then has
only finitely many possible members. A total binary program is complemented
on its entire positive-density column. Each column is computable by a
nonuniform mathematical case split, and finite unions give C_k.

There cannot be a uniform computable sequence of these C_k: on input n one
would take k = v_2(n+1)+1 and obtain X(n) exactly.

The wrapper program h(p) runs the p-th diagonal computation and returns zero
on every input only if that computation halts. Querying X at 2^h(p)-1 decides
the halting question. Hence X has degree 0'. The same uniform wrapper
construction relativizes to X_A having degree A'.

In particular, the exact partner D of X is not below 0'. The proof does not
pretend to construct a c.e. minimal pair with the complete c.e. degree.

## 6. The representative obstruction has the right quantifiers

Density-zero modifications are uniformly coarse equivalent. Every actual
coarse description is therefore a representative in either class. A least
representative must be below each of the two members of the exact pair.

For a numerical representative, its graph is a Turing-equivalent set. If the
graph is computable, the function is computable by searching for its unique
value. A computable representative of X's coarse degree would compute a
computable coarse description of X, which is ruled out by diagonalization.

No inference about the nonexistence of minimal representatives is made.

## 7. The bad-pair relation is Borel for a concrete reason

The apparent quantification over arbitrary common sets is replaced by a
countable union over two oracle-program indices. Their outputs must be total,
binary, equal, and distinct from each of a countable list of core members.
Each condition is a countable Boolean combination of open finite-computation
conditions. Thus Borelness is established in the d-topology.

For fixed U, only countably many possible common sets are below U. The cone
dichotomy makes the bad vertical section meager. The appendix proves the
Borel Kuratowski-Ulam implication rather than assuming that arbitrary relations
with small sections are meager (which would be false).

## 8. The perfect-family construction handles all pairs together

The Mycielski recursion chooses a tuple in a finite product of parent open
sets satisfying all required pair conditions simultaneously. The relevant
coordinate-pair projections preserve the density of the open conditions.
One cannot simply choose the child centers independently and hope that all
cross-pairs work. Shrinking balls then preserves the finite collection of
open pair requirements on products of closures.

Removing pairs involving the countable set C_X intersect L(X) prevents
comparability of distinct selected members. The ordinary product-topology
Cantor-set claim follows from the continuous identity map from d to that
topology, plus compactness of the parametrizing Cantor space.

## 9. Prescribing the core really adds both inclusions

Relative diagonalization alone gives K_(X_A) contained in L(A), not equality.
The even component I(A) of Y_A supplies the missing lower inclusion: every
coarse description projects to a description of I(A), whose block majorities
recover A up to finite error.

The odd component supplies two other properties independently:
- no A-computable coarse description of Y_A can exist, because its odd
  projection would describe X_A;
- the A-computable finite-column approximants have error norm at most
  2^(-k-1), giving the upper inclusion K_(Y_A) contained in L(A).

The odd component also has degree A', so Y_A is not merely bounded by A': it
has exactly that degree. A least representative's graph would belong to the
core and hence be below A, contradicting nonattainment.

## 10. Uniformity, historical status, and formal verification

The negative examples apply to both uniform and nonuniform coarse classes.
The characterization by I(A) is proved only for nonuniform equivalence.
Majority decoding requires a nonuniform finite correction; it is not a uniform
exact extractor of A from every coarse description.

Density-zero modifications are not automatically effective-dense equivalent,
so no answer to C2 is claimed. The negative C1 conclusion follows from older
published results. The report supplies further formulations and full proofs
without asserting first publication.

The Python suite checks only finite arithmetic and a finite stage diagnostic.
No finite output establishes an infinite density limit, Turing nonreducibility,
or an exact pair. No Lean or other formal proof checker was run.
