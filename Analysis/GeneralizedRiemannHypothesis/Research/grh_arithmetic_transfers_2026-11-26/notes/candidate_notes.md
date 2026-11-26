# Exact congruence depth for the Selmer global term

## Executive finding

There is a concrete sharpening of a reusable internal ingredient of `grh-lean`, independent of RH and GRH. Under the same integral matrix-span hypothesis already used by the source, the global conjugate-dual congruence term is exactly the minimum valuation of a trace discrepancy. Its finite-level modules are cyclic. Consequently a scalar-discrepancy estimate loses **no rank factor**: the source bound `d * v(Delta)` improves to `v(Delta)`.

This is an application and repackaging of classical representation theory, especially Carayol's trace-rigidity theorem. It is **not a new theorem in representation theory**, and it does not solve BSD, Bloch--Kato, or another major open conjecture. Its added value for this project is a precise, computable interface for testing new Selmer inputs and a genuine strengthening of an upstream estimate. It extends the prior structural report from the rationally self-dual case to the finite, non-self-dual congruence case.

## Sources, checked 2026-11-26

Upstream commit: `72fead102f663d5c7a407964a13dc0cf9d977207`.

1. `grh/src/New/Congruences/Selmer/SelmerData.lean`, lines 59--77: `conjDualHom` and `congruenceTerm`; lines 105--151: `SelmerDatum`; lines 675--716: scalar annihilation and `congruenceTerm_le`.
   URL: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Congruences/Selmer/SelmerData.lean
2. `grh/src/New/Congruences/Selmer/MainSummands.lean`, lines 145--179: `IsMainSummandLike.normLength_congruenceTerm_le`; lines 65--100: conjugate-dual scalar identity.
   URL: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh/src/New/Congruences/Selmer/MainSummands.lean
3. `grh/src/New/Congruences/Selmer/GeneralTheorem.lean`, lines 367--438: the general simultaneous twisting theorem. The finite global term is part of a full SelmerDatum, not a substitute for its other hypotheses.
4. Prior report `grh_structural_transfers_2026-11-25.zip`, `sections/duality.tex` and `sections/symmetry.tex`: exact Smith formula for arbitrary pairs, rational self-duality obstruction, anticyclotomic invariance, and exact sign dichotomy when the rational intertwiner is nonzero. The report does not state the finite-case cyclicity/trace-depth formula below. An `rg` search through all 46 extracted report archives found no Carayol/trace-depth result.
5. Henri Carayol, *Representations and Pseudo-representations*, RIMS Kokyuroku 884 (1994), pp. 24--26, Theorem 1. Primary source: https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/0884-03.pdf . Theorem 1 states that equal traces and an absolutely irreducible residual representation imply equivalence over a local ring. Browsing ref: `turn376704633view0` (parent must open itself before citing).
6. Henri Carayol, *Formes modulaires et representations galoisiennes a valeurs dans un anneau local complet*, Contemporary Mathematics 165 (1994), pp. 213--237. Bibliographic data checked in Jean-Pierre Serre, *Representations lineaires sur des anneaux locaux, d'apres Carayol*, 1993, notes by R. Rouquier: https://www.numdam.org/item/CJPS_1993__14_/ . Browsing ref `turn376704633view1`.

## The exact theorem

Let O be a DVR with uniformizer pi, fraction field F, and residue field k. Let rho and sigma be representations of an arbitrary group G on free O-modules of the same positive rank d. Assume

    span_O rho(G) = M_d(O) = span_O sigma(G).

These assumptions hold for rho and its conjugate Tate dual whenever they hold for rho: conjugation of G permutes its elements, inversion permutes its elements, transpose preserves the full matrix module, and multiplying each generator by a unit does not change its span. Equivalently, the reductions are absolutely irreducible (using Burnside plus Nakayama).

Define

    a = min_{g in G} v_pi(tr rho(g) - tr sigma(g)) in N union {infinity},
    H_n = Hom_{(O/pi^n)[G]}(rho mod pi^n, sigma mod pi^n).

Then, for every n >= 1,

    H_n is isomorphic to O / pi^{min(n,a)}.

In particular, length_O(H_n) = min(n,a), and sup_n length_O(H_n) = a. Here O/pi^0 means the zero module, and a=infinity gives length n. No assumption that the residue characteristic is larger than d is needed.

### Proof, step 1: trace rigidity

Put A=O/pi^r. Suppose the two traces agree in A at every group element. The map rho(g) -> sigma(g) extends A-linearly to an algebra automorphism of M_d(A). To see that it is well defined, suppose sum_i b_i rho(g_i)=0. For every h in G,

    tr((sum_i b_i sigma(g_i)) sigma(h))
      = sum_i b_i tr sigma(g_i h)
      = sum_i b_i tr rho(g_i h) = 0.

The sigma(h) span M_d(A), and the pairing (X,Y) -> tr(XY) is perfect over every commutative ring: matrix units pair with their transposes. Hence sum_i b_i sigma(g_i)=0. The map is multiplicative because the chosen generators are group images, and the same argument reverses it.

Every A-algebra automorphism of M_d(A) is inner when A is local. For completeness, let F_ij be the images of the standard matrix units. Each image L_i=F_ii A^d is a rank-one free summand (its reduction has dimension one and A is local). Choose a generator v_1 of L_1, and put v_i=F_i1 v_1. Matrix-unit relations show these v_i are a basis and F_ij v_k=delta_jk v_i. In that basis the automorphism is conjugation. Thus the representations are equivalent modulo pi^r. The converse is immediate from invariance of trace.

This is precisely the classical Carayol mechanism, supplied here with an elementary proof under the full matrix-span hypotheses already available in the source.

### Proof, step 2: finite-level cyclicity

View H_n as a submodule of M_d(O/pi^n). Its pi-torsion is identified by multiplication by pi^{n-1} with

    Hom_{k[G]}(rho mod pi, sigma mod pi).

By absolute irreducibility and Schur's lemma this has k-dimension at most one. For a finite-length module over a DVR, the dimension of its pi-torsion is its number of nonzero cyclic summands. Hence H_n is cyclic or zero. Write H_n isomorphic to O/pi^r for r <= n.

If r>0, a generator X has exact order pi^r. As a matrix modulo pi^n, write X=pi^{n-r}Y, where Y is a matrix modulo pi^r having at least one unit entry. Its equivariance is the intertwining equation modulo pi^r. The reduction of Y modulo pi is a nonzero map between irreducible modules of equal rank; therefore it is invertible, and Y is invertible over O/pi^r. Hence rho and sigma are equivalent modulo pi^r, so r<=a by trace rigidity (or simply by equality of their traces).

Conversely, if s=min(n,a)>0, trace rigidity supplies an invertible intertwiner Y modulo pi^s. Lift its entries modulo pi^n and multiply by pi^{n-s}. The resulting element of H_n has exact order pi^s. Thus r>=s, proving r=min(n,a).

## Sharpening the actual source inequality

Let sigma(g)=chi(g^c) rho(g^c)^(-transpose), where chi is the cyclotomic character and c is complex conjugation. Finite character modules of O/pi^n are free rank one over O/pi^n after choosing a generating additive character, so the matrix theorem computes the source's `conjDualHom` lengths exactly. The choice of additive character does not change the length.

The source proves that, if rho(g)=alpha I and rho((g^c)^(-1))=alpha' I, the scalar

    Delta = alpha - chi(g^c) alpha'

annihilates every finite-level conjugate-dual Hom module. Because that module is cyclic,

    congruenceTerm(rho) <= v_pi(Delta).

Upstream `congruenceTerm_le` instead bounds it by d*v_pi(Delta), using injection into the rank-d character module via evaluation at one cyclic vector. The sharper proof replaces this rank-d ambient estimate by the one-dimensional socle argument. If Delta=0 the bound is infinity and makes no assertion.

The direct corollary to `MainSummands.lean` is

    O.normLength (congruenceTerm ell u)
      <= padicValNat ell D.chosenGroupOrder,

with exactly the hypotheses of `IsMainSummandLike.normLength_congruenceTerm_le`, replacing its right side `card n * padicValNat ell D.chosenGroupOrder`. The rest of its proof already establishes v_ell(Delta) <= that group-order valuation; no new arithmetic input is needed for this isolated improvement. The other local terms in beta retain their existing rank factors. Do not state that the whole Selmer budget, theta-lattice error, or final prime-sum bound improves by d.

## Frobenius certificates

For continuous Galois representations unramified outside S, Chebotarev density and continuity give

    a = min_{v outside S} v_pi(tr rho(Frob_v) - tr sigma(Frob_v)).

Reason: if the minimum over G is the finite integer a, the condition that the trace difference has valuation exactly a is a nonempty conjugacy-invariant open set, hence a union of classes in a finite quotient. An unramified Frobenius class meets it. Conversely every Frobenius is a group element. If all discrepancies vanish, both minima are infinity.

Thus any one nonzero Frobenius trace discrepancy gives a valid upper bound for the global term, without searching for a scalar Galois element. Equality requires a lower certificate: all traces agree modulo pi^a, or an explicit intertwiner modulo pi^a. Testing a finite arbitrary list of primes proves an upper bound only; it cannot certify an exact global value without an additional finite-image/generation theorem.

For modular representations this is potentially a practical Hecke-eigenvalue interface. For the source's dual, the second trace is chi(Frob_v^c) tr rho((Frob_v^c)^(-1)); inverse trace can be read from the characteristic polynomial. The dual/primal Frobenius conventions must be kept consistent. This does not imply new modularity, Selmer vanishing, or central L-value nonvanishing: residual irreducibility, local Selmer ranks, scalar inertia, and the remaining global data are still needed.

## Exact, dimension-dividing-residue-characteristic example

Let G be the free group on x,y,z. Over Z_p, take

    A = [[1,1],[0,1]], B = [[1,0],[1,1]], q=1+p^b (b>=1),
    rho(x)=sigma(x)=A, rho(y)=sigma(y)=B,
    rho(z)=I, sigma(z)=q I.

The four group images I,A,B,AB are an integral matrix basis: their vectorized determinant is +/-1. Equivariance with A and B forces an intertwiner to be scalar; the z relation is p^b t=0. Therefore H_n is cyclic of length min(n,b). The source-style rank bound is 2b, while the sharp bound is b.

For p=2,b=3, tr rho(z)-tr sigma(z)=-16 has valuation 4. The single scalar trace loses one bit because d=2 is divisible by p. But tr rho(zxy)-tr sigma(zxy)=-24 has valuation 3; this matches the exact module length. The theorem avoids dividing by d and is valid even at p=2. The exact relation matrix has Smith factors 1,1,1,p^b.

This is an algebraic example, not a claimed Galois realization or admissible Selmer datum. It can also be put in conjugate-dual form with trivial c, rho as above, and a character chi with chi(x)=chi(y)=1, chi(z)=q: the usual alternating matrix identifies rho^dual with rho on x,y. This observation illustrates the algebra but does not supply a CM arithmetic instance.

## Research direction and limitations

The realistic target is a reusable Lean theorem replacing an overly large global budget by a trace-congruence certificate, then a worked arithmetic instance whose remaining hypotheses can actually be checked. It is more concrete than another abstract nonabelian zero criterion. The formalization should split into finite-module cyclicity, trace rigidity, exact length, conjugate-dual identification, and the source estimate corollary.

No Lean compiler is present in this executor as of the inspection. The supporting Python script checks exact finite matrix identities and Smith factors, plus finite kernels in small rings; it is not a Lean formalization and not a build of upstream.

The classical status is explicit: Carayol already supplies trace rigidity, and the cyclicity/length formula follows from standard DVR module structure. The connection to this particular `congruenceTerm`, the rank-factor removal, and the proposed Frobenius-certificate interface are the present analysis. An open-conjecture claim would require additional arithmetic work not present here.
