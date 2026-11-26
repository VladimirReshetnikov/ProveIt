# Transfer analysis: an explicit comparison for the odd cocycle bound

Repository snapshot: `lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.

## 1. A completed bridge, rather than an unproved K-theory application

The source explicitly says that its cocycle module `shaOdd` is not identified
with a standard Tate–Shafarevich group. That comparison can be supplied, for
positive Tate exponents and odd coefficient primes, by an elementary
cohomological argument. This is a useful mathematical extraction from the
repository. It is not a new solution of Vandiver, and no priority claim for the
underlying comparison is warranted: the ingredients are standard.

### Source data

The exact definitions occur in
`grh/src/Lib/GaloisRep/Main/SelmerModules.lean`, lines 154–208:

* coefficients have Galois action `cyc^{-e}`;
* for `e > 0`, `shaLocalSet` is the union, over places above ell, of
  decomposition-group elements whose cyclotomic character is 1;
* the actual cocycle is unramified off ell (it is zero on those inertia groups);
* it satisfies `z(c g c) = -z(g)`;
* cocycles are **not** divided by coboundaries.

`grh/src/Lib/Cyclotomic/OddSha.lean`, theorem
`New.exists_length_shaOdd_le` (lines 645 onward), states that for a CM field
`E` embedded in `Q(mu_N)` and a positive cutoff `t`, there is an integer

    1 <= X <= 2^[4 (N+t+3)^27] h_E

such that, simultaneously for every prime ell, every allowed coefficient ring
`O` with enough roots of unity, every `e<t`, and every `n`,

    length_O shaOdd(ell,E,O,e,n) <= v_O(X).

Here `O` is the integers of a finite extension `F/Q_ell`; `v_O` is the integral
valuation, normalized at a uniformizer. The source's additional roots-of-unity
hypothesis is `HasEnoughRootsOfUnity O (Monoid.exponent (ZMod N)^×)`.

### Definitions for the comparison

Fix an odd prime ell, a CM number field E inside a cyclotomic field, an allowed
coefficient ring O with fraction field F, and an integer e>0. Write

    A_n = (O/ell^n O)(-e),      A = (F/O)(-e).

Let `G_E` be the absolute Galois group. Fix complex conjugation `c` in `G_Q`;
it normalizes `G_E`. For each finite place v fix a decomposition group `D_v`
and inertia group `I_v`. For v dividing ell put

    K_v = D_v intersect ker(chi_ell).

Define S_n to consist of continuous cocycles `z:G_E -> A_n` such that

1. z is zero on I_v for v not dividing ell;
2. z is zero on K_v for v dividing ell;
3. z(cgc)=-z(g) for every g.

This is precisely the source's `shaOdd` for e>0 after suppressing the one-point
matrix-coordinate index. Define the usual full local kernel

    Sha^1(E,A) = ker[H^1(G_E,A) -> product_v H^1(D_v,A)].

All cohomology is continuous. E is totally imaginary, so infinite places add
no condition. The natural complex-conjugation action on cochains is

    (c dot z)(g) = c(z(c^{-1}gc)) = (-1)^e z(cgc).

This coefficient action must not be omitted.

### Comparison theorem

There is a canonical O-linear isomorphism

    colim_n S_n  ~=  Sha^1(E,(F/O)(-e))^{c=(-1)^(e+1)},

where the transition `A_n -> A_{n+1}` is multiplication by ell and is identified
with the inclusions `ell^{-n}O/O subset ell^{-(n+1)}O/O`.

#### Proof, step 1: odd cocycles have no coboundaries

Let Tz(g)=z(cgc). The cyclotomic character is unchanged by conjugation, so T
preserves cocycles and T^2=1. A coboundary is

    delta(a)(g) = (chi_ell(g)^(-e)-1)a.

Thus T(delta(a))=delta(a). Since 2 is invertible on A and A_n, a T-odd
coboundary is zero. The map from odd cocycles to H^1 is therefore injective.
Every class with T=-1 has the unique odd representative

    z^- = (z-Tz)/2.

Indeed its cohomology class is ([z]-T[z])/2=[z]; any two such representatives
differ by an odd coboundary. The local conditions used here are preserved by
T because complex conjugation permutes the relevant places and preserves
the cyclotomic kernel.

#### Proof, step 2: the local condition above ell becomes full local triviality

The image Gamma_v=chi_ell(D_v) is an open subgroup of Z_ell^×: E_v is a finite
extension of Q_ell and hence has finite intersection with the cyclotomic
Z_ell-extension. Its pro-ell subgroup Gamma_v^0 is isomorphic to Z_ell and
has prime-to-ell index. Choose a topological generator u of Gamma_v^0. Since e>0, u^{-e}-1 is nonzero. Standard procyclic
cohomology gives

    H^1(Gamma_v^0,A) = A/(u^{-e}-1)A = 0,

because A=F/O is divisible by every nonzero element of O. Inflation-restriction
through the finite group Gamma_v/Gamma_v^0, whose order is invertible on A,
then gives `H^1(Gamma_v,A)=0`. Inflation-restriction for

    1 -> K_v -> D_v -> Gamma_v -> 1

shows that restriction `H^1(D_v,A) -> H^1(K_v,A)` is injective. K_v acts
trivially on A, so every coboundary restricts to the zero cocycle there.
Consequently a cocycle z whose restriction to K_v is zero defines a locally
trivial class at v, and conversely a locally trivial class has representatives
zero on K_v. This step applies to the divisible coefficient A, not in general
to each finite A_n.

#### Proof, step 3: unramified classes away from ell are already locally trivial

At v not dividing ell, A is unramified and arithmetic Frobenius acts by
`(Nv)^{-e}`. An unramified local class lies in

    H^1(D_v/I_v,A) = A/[(Nv)^{-e}-1]A = 0.

Again the scalar is nonzero because e>0, and multiplication by it on F/O is
surjective. Conversely a locally trivial class restricts to zero on I_v, since
I_v acts trivially and therefore all coboundaries vanish on I_v.

#### Proof, step 4: finite coefficients exhaust the representatives

Every continuous cocycle from compact G_E to discrete A has finite image, so
its image is contained in `ell^{-n}O/O` for some n. Steps 2 and 3 identify
the cocycles satisfying the source's local conditions with representatives of
the full local kernel. Step 1 identifies the odd representatives with its
T=-1 eigenspace. The natural c action is (-1)^e T, hence its eigensign is
(-1)^(e+1). This proves the asserted isomorphism.

### Explicit corollary from the repository

For E,N,t as above choose the single integer X supplied by the Lean theorem.
Then, simultaneously for every odd ell, every allowed O, and 0<e<t,

    length_O Sha^1(E,(F/O)(-e))^{c=(-1)^(e+1)} <= v_O(X).

In particular this standard cohomological eigenspace is finite, is annihilated
by X, and vanishes whenever ell does not divide X. If the residue field of O
has q elements, its cardinality is at most `q^{v_O(X)}`.

To justify passing the bound to the direct limit, the maps S_n -> S_{n+1}
are injective on actual cocycles. Their lengths form a nondecreasing sequence
of integers bounded by v_O(X). This sequence reaches its maximum, after which
every inclusion is an isomorphism: its quotient has length zero. The direct
limit is therefore a finite-length module with the same bound. A module of
length r over a DVR is killed by the r-th power of its maximal ideal; since
v_O(X)>=r, X kills it. There is no asserted effective bound for the stabilization
index n from the length bound alone.

### Further exact corollary: integral odd cocycles vanish

If a continuous cocycle `z:G_E -> O(-e)` obeys the same unramified, local,
and odd conditions, then z=0. Each reduction modulo ell^n lies in S_n and is
killed by X, so for every g,

    X z(g) belongs to intersection_n ell^n O = 0.

Since X is nonzero and O is torsion-free, z(g)=0. This is a precise integral
vanishing statement extracted from the uniform finite-level bound; it is not
vanishing of all torsion cohomology and is not a K-group vanishing theorem.

## 2. Why this does not prove Vandiver or the even K-group conjecture

Alpoge's remark, page 4 footnote 6, tentatively suggests K-group vanishing and
cyclicity up to about degree 100. It is a research suggestion, not one of the
five public Lean endpoints. Source:
https://alpo.ge/remark.pdf (web ref `turn721007067view0` / `turn437438141view0`).

There are three distinct obstacles, now better separated.

**Parity.** The negative precomposition eigenspace in the source is the natural
c eigenspace `(-1)^(e+1)`. Any class descended from Q is fixed by the natural
c action. For e even, the source comparison thus controls the *opposite*
eigenspace, and the two have zero intersection at odd ell. The standard
cohomological target relevant to K_{4m}(Z) has Tate weight 2m+1 in H^2; its
dual H^1 coefficient has exponent -2m, i.e. e=2m even. Therefore the bound
above, by itself, does not control the Vandiver obstruction sector. Further
information from the repository's separate even-class machinery would be
needed. The argument here does not claim a completed K-theory comparison.

**A bound is not vanishing at its exceptional primes.** X can be divisible by
ell. The inequality allows a nonzero group of length up to v_O(X); it does not
force it to vanish. The global upper bound on X is enormous and cannot replace
the arithmetic identification/factorization of a suitable annihilator.

**The quantified field is fixed.** X depends on E,N,t before ell varies.
Substituting E=Q(mu_ell) changes E,N, and X with ell. A statement saying that
only finitely many primes are bad for each fixed E does not say that the
diagonal prime ell is good in its own cyclotomic field.

The classical cohomology/class-group/K-group connection and its parity are
discussed explicitly in Masato Kurihara, “Some remarks on conjectures about
cyclotomic fields and K-groups of Z,” Compositio Math. 81 (1992), 223–236,
especially the introduction and sections 1 and 3:
https://www.numdam.org/item/CM_1992__81_2_223_0.pdf
(web ref `turn542244945view1`). Its introduction states the equivalences of
Vandiver with H^2 of odd Tate weight vanishing, and odd class-group cyclicity
with H^2 of even Tate weight cyclicity. Modern K-theory identification details
are additional literature, not part of this source extraction.

## 3. Concrete non-Dirichlet target and what remains missing

The most economical field target already identified in a prior report is
F=Q(alpha), alpha^3-alpha-1=0, discriminant -23. Let K=Q(sqrt(-23)), whose
class group has order three, and let psi be a nontrivial class-group character.
The two-dimensional induced representation has entire Hecke L-function
L_K(s,psi), and

    zeta_F(s)=zeta(s)L_K(s,psi).

Once the source's Dirichlet theorem is available, RH for F is exactly RH for
that Hecke factor. The source's endpoint does not already include it. This
target is *not new to the incoming reports*; their contribution includes a
positive principal-ideal-class selector and a precise one-sided criterion.

The new comparison above could support the denominator-control side of a
future geometric extension, but it does not supply the essential new local
divisibility detector. Existing data E=Q(sqrt(-d),mu_q) are abelian over Q;
their Frobenius tests are rational congruence/quadratic tests. The cubic
principal-class condition is a nonabelian splitting condition over Q. It needs
new arithmetic input, not a renaming of the existing modulus q.

A theta lift or Hecke L-value appearing internally is not a proof of RH for
that L-function: one must establish a new prime statistic, identify every
residue, prevent cancellation, prove suitable short/spanning/long estimates,
and retain square-root amplification with subpower errors. For an arbitrary
automorphic L-function additional obstacles include signed/complex local
coefficients and missing positive-residue selectors.

## 4. Literature caution for the analytic torsion-specialization extension

The parent/source agent is extending
`New.Selmer.exists_rootsOfUnity_ellVal_eval_le_add` from integral polynomials to
integral power series by truncation on a finite torsion grid. This proof is
sound in principle when all coordinates have strictly positive valuation:
the tail valuations tend uniformly to infinity over the finite grid and the
finitely many reference points. Its value is the *same degree-free conductor
bound*, and it can support simultaneous selected minors/Fitting generators.

Do not claim that p-adic formal-series torsion specialization or simultaneous
nonvanishing itself is new. The source already names these antecedents:

* Vlad Serban, “An infinitesimal p-adic multiplicative Manin–Mumford conjecture,”
  JTNB 30 (2018), 393–408:
  https://www.numdam.org/item/JTNB_2018__30_2_393_0.pdf
  (`turn767131169search7`). Establishes formal-power-series p-power torsion
  rigidity and a Tate–Voloch type separation phenomenon.
* Serban, “On p-adic Versions of the Manin–Mumford Conjecture,” IMRN 2022,
  10279–10301, DOI 10.1093/imrn/rnab136:
  https://academic.oup.com/imrn/article-abstract/2022/13/10279/6291053
  (`turn767131169search4`). Extends rigidity to suitable analytic functions
  and formal groups.
* Daniel Kriz and Asbjorn Christian Nordentoft, “Horizontal p-adic L-functions,”
  arXiv:2310.20678:
  https://air.unimi.it/retrieve/94cce3f5-82ca-4c03-850e-b9b622daed8d/2310.20678v2%20%2814%29.pdf
  (`turn767131169search6`). Includes simultaneous nonvanishing of twists of
  arbitrary finite families of elliptic curves and Diophantine stability.

The extension as presently formulated does not settle a named open
nonvanishing or Iwasawa conjecture: that would require a specific arithmetic
power series/matrix whose hypotheses and relationship to the target Selmer
group are proved, with all specialization error modules controlled.

## 5. Current primary-source endpoint verification

Andrew Sutherland's page for the shorter proof explicitly records commit
72fead10 and that both editions compile, with the five endpoints using only
the three standard axioms:
https://math.mit.edu/~drew/shortgrh/
(`turn582173222search3`).

The corresponding original-proof verification explicitly distinguishes
Dirichlet GRH from general Hecke, Dedekind and automorphic hypotheses:
https://math.mit.edu/~drew/grh/
(`turn582173222search8`).

These are external verification reports. This task did not independently
rebuild the full source or check every transitive dependency.
