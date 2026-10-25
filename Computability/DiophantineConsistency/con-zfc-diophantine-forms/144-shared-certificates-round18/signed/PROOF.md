# Signed spherical digit bounds and an odd-square radix

## Achieved endpoints and logical meaning

The smallest achieved unrestricted-integer endpoint in this directory is `sphere_dimension_centered_merged_odd`: **258 variables, 186 quadratic residuals, degree 4, 5364 nonzero collected monomials, coefficient height 128446**. The corresponding grouped and sparse points have (variables, rows, monomials, height) equal to (263,191,4141,128446) and (285,213,3750,128446). The unmerged sparse point has (286,212,3744,128446). Every equation is literally the sum of the squares of its stored residuals; the complete collected polynomial is also stored.

These are achieved finite constructions, not minimum claims. The statement established in ordinary ZFC is: a displayed polynomial has an integer zero if and only if there is a finite ZFC refutation. Equivalently, its universal nonvanishing assertion is equivalent in ZFC to Con(ZFC). No consistency proof or new end-to-end proof-assistant certificate is asserted.

The calibrated input equations are the three authenticated round17 endpoints `strict_dimension_centered`, `strict_grouped_centered`, `strict_sparse_centered`. The exact input equations and coordinate translations are copied into `source_inputs` and bound by `SOURCE_PINS.json`. The new mathematical changes below are only (i) spherical batching of the eleven digit bounds, optionally merging two batches by exact multiplication, and (ii), in the separately named `_odd` variants, an odd-square replacement for one initial radix-slack sign guard. Every other residual is unchanged, including the complete arithmetic, Horn, frame, anchor, principal-Pell, factorial, and endpoint constraints. Coordinate translations are integral bijections.

The inherited unbounded proof is the round17 `STRICT_BUDGET_PROOF.md`, using `ORIENTATION_FIRST_PROOF.md`, `PROOF_315.md`, the full round16 direct arithmetic proof, and its C222/ZF/ZFC finite-refutation calibration. Those proof texts are copied into `inherited_proofs`, with the complete original source/calibration closure retained in the encompassing release. The new proof below supplies both directions for every changed condition; it does not infer an unbounded theorem from finite testing.

## Semantic notation and unchanged preconditions

Write t,F,V,B,x,y,N,q for the actual semantic values, before harmless integral coordinate centering. The literal source retains

- t=16+h0²;
- V=(F²+1)^t, once its unchanged power request is interpreted;
- FB=V+s0 and B=r0+s0+1, with r0,s0≥0;
- y=V(V−1);
- x=F+1+(y+1)u0;
- x=1+[1+(t+1)y]ut;
- H0=1+the sum of the nine actual encoded representatives;
- N=B^x and q=(BH0)^x, once the unchanged power requests are interpreted.

The prior square frame and signed anchor establish canonical orientation of both coordinates of every principal Pell pair **before** any digit bounds are used. Specifically W=2+sum of the squares of all power atoms, W≥258, |A|>W^W, and all signed requested exponents have absolute value below W. The squared semantic anchor bounds every classified Pell index. The orientation pool, its separated grouped version, or individual sparse residues then give X_k(A),Y_k(A), including signed k and signed A. These arguments use neither the eleven old remainder sign graphs nor the radix-output slack sign graph being changed here.

The unchanged power lemma is consequently available: if the requested base n≥2, the signed exponent k and proposed integer output m satisfy the frame bounds, then the exact power request forces k≥0 and m=n^k. For k<0, multiplication of the Pell congruence by n^(−k) and the huge modulus bound would force m n^(−k)=1, impossible for integral m and n≥2. For base n=1 and known k≥0, the request gives m=1. This is an ordinary integer lemma, valid for either sign of A; no output sign is assumed.

In the baseline sphere variants the old initial guard q−B−1≥0 is retained. Therefore B≥1,q≥2 at the beginning, and the complete round17 pre-factorial recovery schedule applies unchanged. It gives F≥1,B≥2,q≥3, all actual representatives nonnegative, H0≥1, and

    y>F+2,  x≥2+(t+1)y,  N=B^x,  q=(BH0)^x.

In particular x≥6 and N≥2^6≥16. Section 7 below proves the same facts with a new acyclic schedule for the `_odd` variants.

## 1. The exact old digit equations and four denominator groups

Let D_k=q^k. The exact-binomial remainder r_f obeys

    (q+1)^(F²+t)=(B+qH)D_t+r_f.                         (1)

Here H is an unrestricted integer high quotient. Each of the ten range remainders r_a obeys

    (q+1)^a=N D_k Q_a+r_a,                              (2)

with unrestricted integer quotient Q_a. Their upper arguments and lower indices are:

| Group denominator | Remainders / upper arguments | Number |
|---|---|---:|
| D_t | exact-binomial r_f; encoded-index representative | 2 |
| D_(t+1) | encoded a,b,c,d; derived label h | 5 |
| D_(y+1) | encoded S,Sp | 2 |
| D_x | encoded u,vq | 2 |

The old eleven quadratic guards were

    r(D_k−1−r)=a²+b²+c(c+1),                            (3)

which force 0≤r<D_k once D_k>0. In the source labels these are `domain_guard.3` through `domain_guard.13`, grouped as [3,12], [4,5,6,7,13], [8,9], [10,11]. The exact algebraic checker verifies these identities after expanding the recorded coordinate translations.

For each group with common denominator D replace all its guards (3) by the single quadratic guard

    D²−2 Σ r_i²=u²+v²+w(w+1).                         (4)

The three variables on the right are unrestricted integers. The elementary ternary form is nonnegative for every integer triple and represents every nonnegative integer. Its universality follows from the three-square theorem: 4n+1 is representable by three squares, exactly one of which is odd; writing that square as (2w+1)² and the other two as (2u)²,(2v)² gives n=u²+v²+w(w+1).

Equation (4) gives 2r_i²≤D², so |r_i|<3D/4. This weaker rational estimate follows because (3/4)²>1/2. It is enough; no individual sign is presumed.

## 2. A signed low-tail uniqueness lemma

Let q≥2, k≥1, D=q^k, and a≥0. Define the ordinary low tail

    T(a,k)=Σ_(j=0)^(k−1) binom(a,j) q^j.

Binomial expansion gives (q+1)^a≡T(a,k) modulo D. Suppose T(a,k)<D/8 and a proposed integer remainder r satisfies the same congruence and |r|<3D/4. Then

    |r−T(a,k)|<7D/8<D.

Since D divides r−T(a,k), necessarily r=T(a,k). In particular r is nonnegative and smaller than D. This proof explicitly excludes negative impostor representatives; positivity is a conclusion, not an input.

For (1) and (2), their literal equations already imply the needed congruence modulo D. Thus once the small-tail estimates are established, every old interval guard (3) is semantically restored. For a range row, further reduction modulo ND also gives binom(a,k)≡0 modulo N, because N divides q, the lower tail has been removed, and higher terms are multiples of qD. This is exactly the old range predicate, not an approximate replacement.

## 3. The factorial tail is small before factorial identification

It would be circular to use F=t! to establish the first exact-binomial remainder. We do not.

First, for integers M≥1,t≥0 and 0≤j≤t,

    binom(M+t,j)≤(M+1)^t.                               (5)

For j=t this follows from the product ∏_(i=1)^t (M+i)/i, each factor at most M+1. For j<t, induction on t and Pascal's identity bound each of the two summands by (M+1)^(t−1), and 2≤M+1. The j=0 and t=0 cases are immediate (a binomial with lower index −1 is zero).

The canonical t request at base F²+1≥1 gives V=(F²+1)^t≥1 independently of all digit bounds. The retained raw ceiling and B≥1 then force F≥1. Moreover FB≥V≥F²+1, so B>F and B≥2; consequently

    V≤FB<B².

The endpoint schedule gives x≥6, while the exact radix request gives q≥B^x. Hence

    B²≤q/16,  V<q/16.                                 (6)

Apply (5) with M=F². Every coefficient through j=t is at most V. Thus

    T(F²+t,t) < V D_t/(q−1)
                < D_t q/[16(q−1)] ≤ D_t/8.             (7)

The sphere for the D_t group bounds |r_f|<3D_t/4, regardless of the other remainder's meaning. Therefore Section 2 forces r_f=T(F²+t,t).

Reducing (1) after subtraction of this tail modulo qD_t yields

    B≡binom(F²+t,t) modulo q.

The original guard gives 0≤B<q in the baseline variants. The `_odd` schedule below instead proves B<q from q≥B^x. Equation (5) and (6) give 0≤binom(F²+t,t)<q. Thus

    B=binom(F²+t,t).

Now, and only now, the unchanged square-output factorial fixed-point argument applies to the original raw ceiling inequalities, giving F=t!. This restores the exact factorial and product B needed by the CRT and Horn calibration.

## 4. Every other low tail is small

After factorial recovery, the independent, unchanged literal arithmetic row B Q=C0+F²+1 supplies B | C0+F²+1 for the encoded-index representative C0≥0. This row is present before any range decoding; it does not depend on recovery of C0’s interval. Since B>F²+1, C0 cannot vanish, and H0≥2. This is precisely the zero-representative repair in the round17 orientation-first proof.

For any ordinary upper representative a≥0 and any required 0≤j≤k,

    binom(a,j)≤max(1,a)^k≤H0^k.

The actual lower indices t,t+1,y+1,x are all at most x: the endpoint bound x≥2+(t+1)y and y≥1 proves this, and the two strict quotient ranges have lower index exactly x. Hence every such coefficient is at most

    H0^x=q/N.

For the derived label, the unchanged constructor ledger gives h≤H0^ell, ell=4194304. The unchanged factorial bound ell(t+1)<2F and endpoint bound 2F<x imply ell(t+1)<x. Consequently every coefficient of h needed through lower index t+1 is also at most H0^x=q/N. This is the same authenticated derived-label estimate, not a larger unverified degree assumption.

Since N≥16 and q≥2, in every range group

    T(a,k) < (q/N) D_k/(q−1)
             =D_k q/[N(q−1)] ≤D_k/8.                  (8)

Every sphere coordinate therefore satisfies the uniqueness lemma, and all ten old range intervals are restored. All subsequent prime-power precision, residue extraction, local Horn-flow decoding, and finite-refutation interpretation are literally the unchanged round17 proof. In particular all requested nonnegative local data are recovered before applying that calibration.

## 5. Constructive completeness of spherical batching

Start with a finite ZFC refutation. Use the inherited cofinal construction to obtain the semantic values and exact power witnesses. Take the canonical remainders T(a,k), including T(F²+t,t). Bounds (7) and (8) apply to these values. For a group of m≤5,

    2Σ T_i² < mD²/32 < D².

The integer D²−2ΣT_i² is therefore positive and has a ternary representation. Choose one such triple for (4). All remaining residuals already hold by the inherited construction. This proves existence of new witnesses without assuming that every old private witness extends; reconstruction at the semantic level is sufficient.

Conversely, a zero of the new polynomial has every residual zero. The preceding soundness proof restores every old digit interval. Each nonnegative old slack r(D−1−r) has its own ternary representation, so the deleted old guard variables can be filled afresh. Thus the new zero gives a genuine zero of the calibrated old equation (with the unchanged coordinate translation reversed as needed). This establishes the full integer existential equivalence.

## 6. Optional merger of the t and t+1 groups

The `_merged` variants replace the first two spheres by one sphere at denominator D_(t+1). Introduce exactly two product wires

    z_f=q r_f,  z_C=q r_C,

for the two old D_t remainders, and use these two wires together with the five D_(t+1) remainders in (4). The exact interpreted powers give D_(t+1)=qD_t.

Soundness gives |q r_f|,|q r_C|<3D_(t+1)/4 and, since q>0, |r_f|,|r_C|<3D_t/4. Thus the factorial bootstrap and all uniqueness arguments are unchanged. Completeness uses qT_i<D_(t+1)/8 for the two scaled tails and the same estimate for the five others. Now m=7 and

    2Σ (scaled tails)² <7D_(t+1)²/32<D_(t+1)².

The ternary slack again exists. Replacing two ternary triples by one saves three variables and adds two scale wires: net one fewer variable, at the cost of one additional residual. There is no division or integrality assumption in the literal new equations.

## 7. Optional odd-square radix: two additional variables saved

The separately named `_odd` variants remove only the three-variable ternary guard for q−B−1≥0, and add one unrestricted variable z with

    q=(2z+1)².                                         (9)

No old output slack coordinate is silently required to stay nonnegative. The following explicit replacement schedule proves all needed facts.

1. The unchanged squared frame, signed anchor, and coordinate orientation arguments occur first and do not use the removed guard. They still give canonical principal Pell pairs.
2. Since t≥16 and F²+1≥1, interpret its t request directly, including the base-one case. This gives V=(F²+1)^t. Retained r0,s0≥0 give B≥1, F≥1, B≥2, V<B², and y>F+2 as above.
3. Equation (9) gives q≥1, so q+1≥2. Every ordinary actual representative is the exponent of a numerator request at base q+1. The negative-index lemma forces every such representative nonnegative and gives exact numerator values. It also gives h≥0 for the derived-label request; the squared anchor already excludes h=0. Thus H0≥1 is now established, without a factorial or interval assumption.
4. The base BH0 is at least two. Its existing x-index request has output q. The power lemma forces x≥0 and q=(BH0)^x.
5. The first endpoint now rules out u0≤−1, because that would give x≤F−y<0. Hence x≥F+1≥2. The final endpoint forces ut≥1 and x≥2+(t+1)y. In particular q≥B^x≥B²>B, so the missing B<q premise is recovered before exact-binomial recovery. Also q≥4, and every remaining power request, including N=B^x and the denominator requests, is now exact.
6. Sections 3 and 4 recover the factorial digit and every range interval in their stated order. No old guard is used to establish its own replacement.

For completeness, arrange two harmless parities in the cofinal construction. Since y=V(V−1) is even, every beta modulus 1+(i+1)y is odd; adding their odd common CRT modulus allows the beta code x to be chosen even while preserving all encoded values and nonnegative endpoint quotients (choose a sufficiently large representative). After F=t! the factors of B are odd, so N² is odd. Actual encoded representatives can be varied by N² without changing their required residue classes. Choose a,b with opposite parity, as already required to make h even. Independently prescribe the parity of any one of the other seven representatives so that their total sum, including a,b, is even; thus H0 is odd. The dominant a representative can still be selected between 2N² and 4N² with its prescribed parity, while the other representatives stay at most 2N². All inherited dominance and cap bounds remain intact.

Now BH0 is odd and x is even. Let R=(BH0)^(x/2), an odd positive integer, and put z=(R−1)/2. Then q=R²=(2z+1)² as required. The radix, coefficients, CRT precision, and private Pell witnesses otherwise remain the same. This proves completeness of (9), rather than merely adding an unproved square restriction.

## 8. Literal artifacts, reproducibility, and verification boundary

`build_spheres.py` uses only the copied input JSONs in `source_inputs`; it has no dependency on an absolute prior-workspace path and imports no prior builder. It verifies the exact old guard shapes, changes the specified rows, removes only unused coordinates, and emits both residual and expanded polynomial forms for all twelve variants.

`check_spheres.py` does not import the producer or any prior algebra checker. It independently reconstructs each new system in named coordinates from pinned input equations, checks every untouched row, computes every coefficient of each squared residual, and verifies all metrics. Normal and Python `-O` runs pass. Thirty deliberate coefficient mutations across sphere rows, frame rows, and odd-square rows are rejected. Finite Pascal and signed-tail controls are also supplied, but are explicitly not used as substitutes for the proofs above.

Run:

    python build_spheres.py
    python check_spheres.py
    python -O check_spheres.py

The new steps are elementary identities, inequalities, congruence arguments, integer coordinate bijections, and constructive CRT/ternary representations. Together with the inherited ordinary refutation calibration they establish, in ZFC, for every released endpoint P:

    (∃ integer vector v, P(v)=0) ↔ (there is a finite ZFC refutation),

and therefore

    (∀ integer vector v, P(v)≠0) ↔ Con(ZFC).
