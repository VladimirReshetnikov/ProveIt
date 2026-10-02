# Removing representability from the full multivariate theorem

Status: proposed ordinary extension, awaiting independent review. October 1, 2026. The already reviewed representable proof and all delivered packages are unchanged.

## Claim

The polynomial and conclusion of FULL_SELECTED_TAIL_THEOREM.md hold for EVERY finite matroid M on E union {A,B} for which E spans M. No field representation is needed. The graph corollary is unchanged. Only the principal-line seed and M-convex-support constructions need replacement; every derivative identity, boundary argument and old-element contraction step is purely matroidal.

## Primary source facts

Bonin and Kung, *Semidirect sums of matroids*, primary author manuscript https://arxiv.org/pdf/1210.0626, Section 2 defines matroid union by its independent sets and gives its rank formula (2.1). Section 3, Lemma 3.1 gives the rank of an extension by elements freely placed on the flat spanned by a fixed set F:

  r_plus(X union Y)=min(r_M(X union F), r_M(X)+|Y|),        (1)

where X consists of original elements and Y of the added free-on-flat elements. These statements apply to arbitrary finite matroids. The manuscript's Lemma 2.4 also confirms that contraction commutes with union when the contracted element is a loop in one factor, as it is for the old elements in the construction below.

These are the only extra matroid operations used here. A primary foundational reference for the general partition theorem is Edmonds and Fulkerson, *Transversals and matroid partition*, J. Res. NBS 69B (1965), 147–153, Section 4, Theorem 1c; official PDF https://nvlpubs.nist.gov/nistpubs/jres/69B/jresv69Bn3p147_A1b.pdf. The explicit union formulation and principal-extension rank formula used in this note were checked directly in Bonin–Kung.

## 1. Principal-line seed without matrices

Let F=cl_M{A,B}. Add m elements freely on F by the operation in (1). The extension has rank q=r(M). For an old (q-1)-subset I, extension by one new element is a basis exactly when I is independent and r_M(I union {A,B})=q. Since I has rank q-1, this occurs precisely when I+A or I+B is a basis. Thus its polynomial is U, the Boolean union of the two extension families.

For an old (q-2)-subset I, extension by two new elements is a basis exactly when I+A+B is a basis, again directly from (1). The same holds for A plus one new element: apply (1) with X=I+A, obtaining rank q exactly when X is independent and r_M(I+A+B)=q. The B case is symmetric. Finally, the original and new line elements all lie in a flat of rank at most two, so no basis contains three of them.

The exact basis polynomial is consequently

  U0+sA UA+sB UB+(sum_i h_i)U
    +[sA sB+(sA+sB)sum_i h_i+sum_(i<j)h_i h_j]V.

Set h_i=sU/m and take the coefficientwise limit. Matroid-basis Lorentzianity, nonnegative linear substitution and closedness yield exactly the seed

  U0+sA UA+sB UB+sU U
               +(sA sB+sA sU+sB sU+sU²/2)V.

This includes loops, parallel A,B and all ranks, with negative-cardinality families interpreted as zero. It replaces the field-based construction in Section 2 of the representable proof.

## 2. Support matroid as a union

Let Y be the finite collection of private-A, private-B and common weighted heads, and let D={d_y:y in Y} be private dummy elements. On the common ground set E union {A,B} union D, define:

- M1: M extended by loops on D;
- M2: the rank-|Y| transversal matroid with slots Y, where each d_y is adjacent only to y, A and B have their prescribed private/common incidences, and every old element of E is a loop.

Let K=M1 union M2 be their matroid union. Since E spans M, an old basis of size q together with all |Y| dummies is a K-independent set of size q+|Y|. No union-independent set is larger than the sum of the two ranks. Therefore r(K)=q+|Y|.

Every K basis J has a partition into an M1 basis of size q and an M2 basis of size |Y|. Indeed an independent union decomposition may be made disjoint by removing overlaps, and the total basis cardinality forces both factors to attain their full ranks. Old elements must be in M1, while dummy elements must be in M2. Only A and B can be assigned to either factor.

If r dummies are omitted from J, exactly r distinguished elements must be assigned to M2. Hence r<=2. The resulting basis cases are precisely those in the representable proof:

- r=0 gives U0+aUA+bUB+abV;
- r=1 and one distinguished element selected gives its allowed head incidence times U0;
- r=1 and both distinguished elements selected gives UB for a private-A head, UA for a private-B head, and U for a common head;
- r=2 gives U0 exactly when the two omitted heads can match A,B.

Different partitions of the same basis are not counted more than once. In particular, the common one-head case is the Boolean union, not the sum of two possible allocations.

Specialize the dummy variables to z/omega_y and multiply by product_y omega_y, initially for positive head weights. The basis polynomial of K becomes z^(|Y|-2)F_M, with exactly the polynomial F_M defined in the representable note. Zero weights follow by the explicit coefficient limit. The old-basis term remains nonzero. Its support is M-convex, and the monomial exponent translation therefore proves M-convex support for F_M.

## 3. Completion of the proof

For an old nonloop e, differentiating each of U0,UA,UB,U,V restricts its subsets to those containing e and then deletes e. This gives exactly the same five families for M/e, whose remaining old ground set spans rank q-1. The Boolean union operation commutes with this restriction. No representation is involved.

Thus Sections 4–8 of FULL_SELECTED_TAIL_THEOREM.md apply unchanged: the q0 quadratic, q1 loop indicators and Schur complement, q2 seed substitutions minus nonnegative Hessian diagonals, q3 special-direction derivatives, q4 contraction basis V, and vanishing remaining derivatives at q>=5. The full multivariate Lorentzian theorem follows for every finite matroid M with a spanning old ground set.

This is an ordinary extension, not an inference from finite checks. A separate final review must approve the replacement constructions and the resulting unrestricted statement. It still treats the Y-population weights as parameters and does not authorize physical tail/head role merging or a general rank-six support theorem.
