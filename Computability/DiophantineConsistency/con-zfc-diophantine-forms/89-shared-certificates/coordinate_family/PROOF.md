# Baseline reproduction: residue orientation, determinant guards, and selective elimination

## Statement and scope

All quantified coordinates in this note are **unrestricted integers**. The
five equations constructed below have zeros exactly when the fixed syntactic
ZFC calculus calibrated by the source repository has a finite refutation.
Consequently, ordinary mathematics formalizable in ZFC proves that each
equation has no integer zero if and only if Con(ZFC).

This file documents an independently reproduced baseline, not a new result.
All size points listed here are already present or dominated in the incoming
archives reviewed later in this session. The new results are in
COORDINATE_PROOF.md and coordinate_section.tex: 21 integers at degree 16,
20 at degree 18, and 19 at degree 40.

The baseline is a verified composition and refinement of existing source
mechanisms. The current overview already proposes combining residue
orientation with the determinant guard. We do not claim that this combination
was previously unexplored, a globally smallest equation, or an externally
peer-reviewed theorem. The important additional choice is to retain one
coordinate while merging the remaining guards: eliminating every available
coordinate first would lose the degree-eight result.

| Equation | Integer coordinates | Residuals | Exact total degree |
|---|---:|---:|---:|
| quartic37 | 37 | 24 | 4 |
| sextic31 | 31 | 18 | 6 |
| octic25 | 25 | 13 | 8 |
| dodecic24 | 24 | 12 | 12 |
| degree16_23 | 23 | 11 | 16 |

For historical comparison against the numbered collection only, at pinned commit
08200eb10fde2db408c69dffd840d6920a569b1f the inspected overview reports
38 integers at degree four, 32 at degree six, 27 at degree eight, and 26
at degree sixteen. The separately known ten-integer high-degree equation
is not improved in variable count. Expanded expression size increases. This historical comparison is superseded
by the incoming archive review; it is not the novelty comparison for the new
coordinate family.

The finite verifier checks exact polynomial identities and all coefficient
bytes. The proof uses the explicit inherited native-compiler, signed-Pell,
and K215/refutation theorems; this package is not a new end-to-end Lean/Rocq
certificate or an internally encoded derivation in the object ZFC calculus.

## 1. Fixed numerical coefficients

Use the complete source-34 tuple, not a mixture of tuples:

    beta = 2^1064921 - 1,
    K0, MC, MF = the source-34 literal integer payloads,
    A = 2^1113,
    B = 2^666104.

Here MF is already shifted. The six actual integer byte strings are in
coefficients/, and COEFFICIENT_BINDING.json binds every port. The native
four integers are reconstructed from the retained 430-row k215.tm and
943-tile list by the byte-authenticated source-34 constructor. The two
new scales are pure powers of two. Total minimal unsigned coefficient
payload size is 615,883 bytes, unchanged from source 71. All coefficients
are fixed by finite recipes independent of consistency or a refutation search.

The relevant elementary fixed facts are beta=1 mod 3,
0<MC<beta<MF<2 beta, K0>=0, and A,B>=2.

## 2. The single equation in 25 unrestricted integers

Take the following 25 coordinates:

    J3,F,alpha,z,f,h,r,v,w3,tau,eta,zeta,y,gamma,o,j,E,c,a,V,I,
    t,p1,p2,p3.

The variable names in the JSON use v_scale for v, pair_root for t,
and pair_pos1,...,3 for p1,...,3. Define polynomial abbreviations only:

    J0 = 3 J3 + 1,
    W = 4(3 w3 + 1),
    q = beta J0 + 1,
    C = q - F - alpha,
    k = eta + zeta,
    X = W q,
    Delta = a^2 + 4a + 3,
    D = X + a c + gamma(4a+3),
    P = k + E(c-eta),
    R = (q-F)(q^3-q) - C(q^2-1) + (MC+q MF)J0,
    G = A F B C - (q-A F-B C)^2,
    Z = eta zeta,
    Pos(p1,p2,p3) = 1+p1^2+p2^2+p3(p3+1).

No abbreviation is a further quantified unknown. The equation is

    Q25 = r1^2 + ... + r13^2 = 0,

where the complete residual list is:

    r1  = a-E-(2v+1)q^3,
    r2  = E+(E-a)X,
    r3  = c-eta+(E-a)k,
    r4  = tau^2-P^2+Pk-1,
    r5  = D^2-Delta c^2-1,
    r6  = k-1-hE-R,
    r7  = (K0+W)C-z(q-1)-F,
    r8  = V+c-fo,
    r9  = V-jc+k-1-hE,
    r10 = I-(2r+1)c^2,
    r11 = I^2-Delta(f^2-1),
    r12 = y^2-1-I^2(y^2-V^2),
    r13 = GZ-(t^2-G-Z+1)^2-Pos(p1,p2,p3).

The machine-readable equations/octic25.json expands all these expressions
literally. Each residual has degree at most four. Only r13 uses t, and its
t^4 coefficient is -1. Hence [t^8] Q25=1 after the numerical coefficients
are specialized, proving exact total degree eight.

## 3. The two positivity facts used in the construction

### Lemma 1: ternary positive values

Pos(u,v,w) is positive for all integer u,v,w, since w(w+1)>=0. Conversely,
every positive integer n is such a value. Legendre's three-square theorem
applies to 4n-3: it is positive, is 1 or 5 modulo 8, and is not divisible
by 4. A three-square representation has one odd and two even squares.
Writing them as (2w+1)^2,(2u)^2,(2v)^2 gives n=Pos(u,v,w).

### Lemma 2: the nearest-square pair guard (source 68)

For integers x,y, define

    H(x,y,t)=xy-(t^2-x-y+1)^2.

Then x>0 and y>0 if and only if H(x,y,t)>0 for some integer t.

For soundness, H>0 implies xy>0. If both x=-a and y=-b were negative,
with a,b>=1, then (t^2+a+b+1)^2>ab, contradicting H>0. Thus both are
positive. For completeness set N=x+y-1>=1 and m=floor(sqrt(N)). Choose
t=m when N-m^2<=m, and t=m+1 otherwise. If N is a square the error is
zero. Otherwise |t^2-N|<=m and m^2<N. Therefore

    (t^2-N)^2 < N <= xy,

the last inequality being equivalent to (x-1)(y-1)>=0. Combining with
Lemma 1 proves the precise existential equivalence

    x,y>0  iff  exists t,p1,p2,p3:
      xy-(t^2-x-y+1)^2=Pos(p1,p2,p3).

Four unrestricted witnesses replace two independent triples. This is an
existential equivalence, not a bijection between guard witnesses.

### Lemma 3: determinant soundness (source 71)

Put U=A F, Vc=B C, G=U Vc-(q-U-Vc)^2, where A,B>=2 and
alpha=q-F-C. If G>0 then F,C,alpha have one common strict sign.

Indeed U,Vc have the same nonzero sign, and

    |q-U-Vc| < sqrt(U Vc) <= (|U|+|Vc|)/2.

Thus q has their sign and
|q|>(|U|+|Vc|)/2>0. Since A,B>=2, this is at least |F|+|C|,
with strict inequality for |q|. It follows that alpha=q-F-C has the same
nonzero sign. In particular F alpha>0 and F C>0.

For completeness the inherited source-34 canonical witnesses satisfy

    q/2 <= A F < 4q/5,  q/2 <= B C < 3q/5.

These exact uniform bounds are proved in the retained source-71 note from
canonical leading digits, without making assumptions about an arbitrary
zero. Writing A F=q/2+x, B C=q/2+y gives G>3q^2/25>0. The estimates
remain valid for every allowed rank-tuning choice and every canonical
tableau size. Hence the same canonical witnesses used for the residue
restrictions below also satisfy this guard.

## 4. Quartic37: combining the two semantic interfaces correctly

Start with source 71's literal quartic38, retained as quartic38.json.
It has a determinant guard G=Pos(cone_pos1,cone_pos2,cone_pos3), a guard
eta zeta=Pos(eta_zeta_pos1,eta_zeta_pos2,eta_zeta_pos3), and the separate
row X=2u^2. Replace J by 3J3+1 and w_scale by 3w3+1, then delete the
row X-2u^2 and its variable u. The remaining 24 rows use 37 variables
and remain quadratic. The tau^4 coefficient of their sum of squares is 1.

Soundness is a composition in the following order. A new zero has G>0.
Lemma 3 allows the two old positive guards F alpha and F C to be supplied
with fresh Pos triples. Together with the affine J and w_scale restrictions
and all unchanged arithmetic rows, this is exactly a zero of the source-70
affine quartic40. Its sign-uniform Pell argument first recovers X=+/-2^R
with R odd before assuming X positive. Since beta=1 mod 3, the restrictions
give q=2 mod 3, W=1 mod 3, and X=qW=2 mod 3. The negative power branch
has residue 1, so X=2^R. Therefore u=2^((R-1)/2) restores the deleted
square guard, and the source theorem supplies a finite refutation.
There is no use of a positive-X theorem before the guard is restored.

For completeness a finite refutation supplies the canonical source-34
family used in source 70, with q=2^s for odd s, R odd, and R-s-2 a
nonnegative even integer. Thus J_old=(2^s-1)/beta is 1 modulo 3,
w_old=2^(R-s-2) is 1 modulo 3, and the new integer J3,w3 exist.
The source-71 determinant estimates apply uniformly to this same
canonical family and provide a positive G. Lemma 1 supplies its new
triple. Keep the other canonical coordinates and remove u. This yields
a zero of quartic37.

The initial transformation preserves existence through canonical witnesses.
It is deliberately not claimed to preserve every old zero.

## 5. The polynomial projections and their restoration maps

Whenever a source row is v-P(other coordinates), deleting that row and
substituting P everywhere gives a bijection of integer zero sets. Forgetting
v and restoring it by P are inverse maps. Every projection below uses this
principle with literal integer polynomials; no division or sign restriction
is hidden in a restoration.

### Sextic31

From quartic37, put q=beta(3J3+1)+1, W=4(3w3+1), k=eta+zeta. Eliminate

    N=q(L+1), X=Wq, C2=c^2, F2=f^2, g=y^2-V^2,
    P=k+E(c-eta),

and replace tau_old by tau_gap+E(c-eta). The first norm becomes exactly

    tau_gap^2+(2 tau_gap-k)E(c-eta)-1.

Its quartic leading terms cancel, leaving degree three. All other rows
are at most cubic. Six variables and six defining rows disappear, giving
31 variables and 18 rows. The only row involving r is I-(2r+1)c^2, so
[r^2 c^4] Q31=4, proving exact degree six.

### Octic25: retain zeta before merging guards

From quartic37 eliminate ten coordinates:

    L=q^2-1, N=q^3, X=Wq, C2=c^2, F2=f^2, g=y^2-V^2,
    Baux=I^2, D=Wq+ac+gamma(4a+3), Delta=a^2+4a+3,
    P=k+E(c-eta).

Keep zeta as a quantified coordinate. There are then 27 variables and
14 rows. The two remaining guard quantities are G of degree two and
Z=eta zeta of degree two. Replace their two independent Pos rows (six
variables) by the single equation from Lemma 2 (four variables). This
leaves 25 variables and 13 rows, exactly the formula in Section 2.
Its degree is eight by the private t^8 certificate already given.

### Dodecic24: now eliminate zeta

In octic25 the ninth row is monic in zeta. Set

    k=1-V+jc+hE, zeta=k-eta,

and delete this row and coordinate. This is another integer-polynomial
zero-set bijection. All arithmetic rows remain of degree at most four.
The guard quantity Z=eta(1-V+jc+hE-eta) now has degree three; the combined
guard has degree six, so its square has degree twelve. Its term
-eta^2 h^2 E^2 is the unique source of eta^4 h^4 E^4 in the sum of
squares, with coefficient 1. Thus the 24-variable, 12-row equation has
exact degree twelve.

This is the reason retaining zeta was essential at degree eight: applying
the pair guard after eliminating zeta would have produced this dodecic,
not a purported octic.

### Degree16_23

Finally eliminate I=(2r+1)c^2 from dodecic24 using its monic defining
row. There remain 23 integer variables and 11 rows. The auxiliary norm
becomes

    y^2-1-(2r+1)^2 c^4 (y^2-V^2),

of degree eight; the joint guard remains of degree six. No other row can
contribute r^4 c^8 V^4, whose coefficient in the single sum of squares is
16. Hence the exact total degree is sixteen. This is another polynomial
bijection on the zero sets, and inherits the same refutation equivalence.

## 6. What is proved, what is inherited, and what the checks establish

The formula lists, integer-polynomial restoration maps, variable counts,
degree certificates, and guard-merger proof are explicit above. The
signed-power recovery and canonical determinant bounds are used from the
retained sources 70 and 71. Their conclusions are compatible because both
use the entire source-34 tuple and the same canonical source-34 accepting
family; the determinant bound is uniform over rank tuning.

The native compiler and the literal K215/refutation calibration are inherited.
The artifact does not claim that a finite numerical test proves an unbounded
Pell theorem, proves ZFC consistent, or establishes absence of zeros.

The verifier uses a restricted arithmetic parser and exact integer sparse
polynomials. It confirms all defining rows vanish on substitution, checks
the literal inherited determinant and eta-zeta guards before replacing them,
checks all variables are live and all nonvariable symbols are bound, proves
the exact degree by a nonzero coefficient independent of the fixed ports,
reconstructs all six coefficient numerals, and compares raw integer hashes.
The nearest-square finite controls are expressly diagnostics. They are
not the proof of Lemma 2.

## 7. Further questions

1. Can another coordinate be retained or exchanged to keep all positivity
   quantities quadratic while permitting an additional octic elimination?
2. Can a canonical calibration replace the last two guards with a single
   quadratic guard, rather than the quartic pair guard, without adding a
   hidden sign hypothesis?
3. Can these reductions be rebound to the compact source-44 tuple with
   equally explicit signed-power and determinant-completeness proofs?
4. Can a branch-aware elimination optimizer minimize the pair
   (number of unrestricted variables, total degree) while emitting exact
   integer restoration certificates?
5. Can the signed-power theorem and canonical determinant compatibility be
   formalized end to end in the repository's Lean development?

The first three questions have not been resolved by the present construction.

## Source files retained and exact attribution

* Source 34: coefficient constructor, literal machine and tile list, coefficient
  proof, native language/compiler note, and binding.
* Source 64: Q41 literal packet and the PROOF41/PROOF44 interfaces.
* Source 68: PAIR_GUARD_PROOF.md, the nearest-square positivity lemma.
* Source 70: integer/section.tex, the sign-uniform Pell argument and affine
  orientation theorem.
* Source 71: determinant proof, literal quartic38, coefficient binding, and
  exact polynomial engine.

SOURCE_PINS.json records immutable Git blobs and the retrieval commit.
Inherited licenses and notices are retained under upstream/licenses/.
These files are immediate proof dependencies, not a complete duplicate of
every transitive repository formalization or historical paper.
