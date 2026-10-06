# A projective loader for the centralizer word family

The centralizer query `[A^(B^n),T]` admits the existing three-operation
positive7 input loader after two fresh generator names. The conjugating
word T stays fixed. A new Britton argument removes the projective
ambiguity; the graph-group argument in the older projective theorem is
not used. The generic dense/common-column history compiler applies to
the resulting alphabet. The specialized sparse sources do not yet have
this changed alphabet bound into their paid paired-action cut.

This is a handwritten bridge and finite fixed-data specification, not a
matrix evaluation, substituted-word materialization or emitted compiler.
It is conditional on the frozen Accepted interface and its imported
Korec/Higman premises, the proved finite two-generator embedding, and the
established matrix/lift/native-history interfaces specified below. Root
requested the investigation; Aristotle found a five-name version and
Riemann independently improved it to the two-name extension used here.

## 1. The reliable group and four presentation names

Use right conjugation u^v=v^-1*u*v. The centralizer construction gives

    Q=<K,t | t^-1 ell_i t=ell_i, i=1,2,3>,
    F=<a0,b0,c0> <= K,
    alpha=a0^(b0^23), beta=b0^c0,
    F intersect H=<h_j:j in U>, H=<ell_1,ell_2,ell_3>,
    h_j=beta^-j alpha beta^j.                              (1)

The pair alpha,beta freely generates a rank-two subgroup of F. The
centralizer presentation has 499 declared generators and 17679 relators.
Its latest literal-branch companion reports those records; this note
reads the companion, not its large arrays or source comparator.

Apply the full finite universal words from the frozen two-generator
proof. This gives an injective map i:Q->Q2=<x,y|R>, with exactly 17679
declared relator slots. Write A(x,y), B(x,y), T(x,y) for the specified
images of alpha,beta,t. Adjoin only two fresh presentation generators:

    H4=<a,b,x,y | R, a^-1 A(x,y), b^-1 B(x,y)>.            (2)

Eliminating a,b recovers Q2. Thus the copy of Q is still embedded, a and
b denote i(alpha),i(beta), and T denotes i(t). The declared count in (2)
is four generators and r=17681 relators. In the free presentation group
F4=Free(a,b,x,y), these are four independent basis letters. Their quotient
relations must not be imposed on the later faithful free-group matrices.

Let pi:F4->H4 and form

    M={(u,v):pi(u)=pi(v)},
    M_T=(T,1) M (T^-1,1).                                (3)

The exact finite generating list of M_T is

    (T z T^-1,z), z=a,b,x,y;  (1,R_j), 1<=j<=r.          (4)

The usual normal-closure proof of the fibre-product generators applies
to every finite presentation. T need not be a basis letter. Include
both signs of every slot in (4), retaining duplicates and identities:
the signed alphabet has m=2(4+r), hence m=35370 for (2).

## 2. The projective ambiguity is removed by Britton

Use the established faithful index-three Schreier representation

    U0=[1,1;0,1], V0=[1,0;4,1],
    rho(a)=U0, rho(b)=V0^3,
    rho(x)=V0 U0 V0^-1, rho(y)=V0^2 U0 V0^-2.             (5)

Its image Gamma is the kernel of V0-exponent modulo three in the free
group <U0,V0>. All its matrices have diagonal entries 1 modulo four and
lower-left entry 0 modulo four. A lower-triangular member has determinant
one, hence diagonal +1 or -1; the congruence excludes -1. It is V0^j,
and its membership in Gamma forces j divisible by three. Consequently
the exact lower-triangular stabilizer in Gamma is <rho(b)>.

For n>0 define a_n=b^-n a b^n and put r_n=12n. Then

    L_n=rho(a_n)=[1+r_n,1;-r_n^2,1-r_n],
    v_n=L_n^-1 e2=(-1,r_n+1)^T.                          (6)

For any P in Gamma, (P v_n)_1=0 iff P=rho(b)^k L_n for an
integer k; in that case P v_n=e2 exactly. Apply this independently to
both components of the faithful image of M_T. Simultaneous vanishing
therefore gives free words b^k a_n and b^l a_n, with

    T^-1 b^k a_n T=b^l a_n in H4.                       (7)

Every element in (7) belongs to the embedded image of Q. Pulling back
gives, in its identity HNN extension,

    t^-1 beta^k h_n t=beta^l h_n.                        (8)

The right side lies in K. Britton's lemma says t^-1 g t can lie in the
embedded K only if g lies in its associated subgroup H. Thus beta^k h_n
belongs to H. It also lies in F, so (1) puts it in <h_j:j in U>. The
beta-exponent homomorphism on Free(alpha,beta) vanishes on each h_j;
applying it to this subgroup equality gives k=0. Basis-subset membership
in the free family {h_j:j in Z} now gives n in U. Since t fixes H,
(8) then yields beta^l=1 in the embedded free pair, and l=0.

Conversely n in U implies t^-1 h_n t=h_n, so (a_n,a_n) belongs to M_T
and both projective coordinates vanish. This proves the exact equivalence

    n in U iff some (P,Q') in rho(M_T) has
                 (P v_n)_1=(Q' v_n)_1=0.              (9)

No beta-exponent homomorphism on all of K, Q or H4 is assumed. The map
is applied only after obtaining an equality inside Free(alpha,beta).
No decision procedure for H-membership is used.

## 3. The unchanged paid ordinary-input column

For J=[p,q;s,d] use the inherited integral representation

    Sym(J)=[p^2,-2pq,q^2; -ps,pd+qs,-qd; s^2,-2sd,d^2].

It acts on symmetric coordinates (a,b,c) meaning [a,-b;-b,c]. For
tau=12n+1, the vector v_n v_n^T has coordinates (1,tau,tau^2), so

    u6=(1,0,0,1,0,0), v6=(1,tau,tau^2,1,tau,tau^2),
    u6 diag(Sym(P),Sym(Q')) v6
      =((P v_n)_1)^2+((Q' v_n)_1)^2.                    (10)

The signed alphabet (4) therefore has a zero scalar word exactly for
n in U. Its empty word has value 2 and is not accepting. For a fixed
program e and ordinary input x>0, n=2^e(2x+1) gives

    alpha_e=12*2^(e+1), gamma_e=12*2^e+1,
    scaled=alpha_e*x, tau=scaled+gamma_e, tau2=tau*tau.  (11)

These are precisely 2M+1A. No input power, n witness or runtime word
substitution is hidden. The fixed universal alphabet is independent of e.

Apply the inherited seven-dimensional weighted positive lift to this
new six-dimensional alphabet. Its input remains

    z=(3,tau,tau2,2,tau,tau2,1),

and its decoder identity multiplies (10) by 8^length. Thus equality of
terminal coordinates 1 and 7 is equivalent to (9). All letters are
strictly positive integer matrices with one common dyadic column sum C.
The lift's row-sum and coefficient choices must be prepared from this
new alphabet, rather than inherited from the old conjugator-a instance.

## 4. Finite coefficients without flattening substituted relators

The fixed-data recipe can remain a finite word-composition graph. For
the 499 original generator names define the full words

    w_i=y^((x*y^i)^2*x^-1) * (y^-1)^x.

For each old relator retain its old signed-letter list and reference w_i
or w_i^-1 at each occurrence. Retain A,B,T in the same manner; append
the two naming relators of (2). Concatenation, inverse and fixed repetition
are literal finite grammar nodes. This specifies every word in (4)
without storing its fully expanded two-letter string. In particular no
word-problem decision or cancellation is needed.

There is an equally finite integer coefficient recipe: assign the four
matrices (5), interpret concatenation as ordered matrix multiplication,
and interpret inverse by [p,q;s,d]^-1=[d,-q;-s,p]. Apply Sym, the fixed
unimodular lift chart, and the displayed positive-lift formula. These
are definitions of fixed numeral roles, not runtime operations on x.
This note does not execute that recipe or materialize its output integers.

A conservative positivity bound also needs no evaluated word matrix.
Let ell>=1 be a common literal U0,V0 word-length upper bound for every
component in (4), including inverse slots, obtained by addition and fixed
repetition in the composition grammar. In the infinity row norm all
U0,V0 and their inverses are at most 5, so N=5^ell bounds every component.
Each Sym block has norm at most 4N^2. The fixed lift chart and its inverse
each have norm at most 3, so every charted signed letter G has norm
at most 36N^2. Choose

    kappa=2^(10+6ell), C=8kappa.                          (12)

Then 28*36*25^ell < 2^(10+6ell), as 1008<1024 and 25<64.
Thus kappa>28 max row-absolute-sum(G), the exact sufficient condition
in the weighted positive-lift proof. Choose any fixed dyadic K>max(C,m)
for the history geometry. These deliberately loose bounds avoid a
search for a minimal buffer. They are fixed numeral recipes, not extra
existential witnesses or free variable-times-coefficient multiplications.

## 5. Precisely applicable paid compiler and remaining work

The full dense/column6 theorem accepts any fixed strictly positive
seven-dimensional integer alphabet, with the column6 variant requiring
the common column sum C. It has the same ordinary input (11), terminal
alias F7=F1 and exact nonempty-word positive projection. Therefore its
generic family applies to the new lift with the specified fixed roles.
For m letters, ell_pack=8m+2 and pc=floor(log2 ell_pack)+popcount(ell_pack)-1,
its single-polynomial column6 ledger is

    (67m+77+pc)M + (82m+106)A,
    8m+36 positive existential coordinates.              (13)

These figures include native64, every coefficient multiplication, the
three loader rows, geometry/selection/history and the 23-comparison
sum-of-squares finalizer. This note derives applicability of that already
proved family; it has not emitted or audited the m=35370 specialization.

The concrete remaining paid/source work is to bind the already independently
authenticated centralizer prefix to the full-word/naming recipes, bind every new fixed matrix role and
buffer/geometry numeral, and emit/audit a complete instance of the generic
grammar (or a separately proved sparse replacement). Storing fully expanded
substituted word strings is not mathematically necessary: their finite
composition graph gives an exact alternative specification. Numerical
matrix expansion, actual complete-source evidence and a claim about the
resulting numerical universal bound remain separate tasks.

## 6. Retained boundaries and credited questions

**Remark 1 (valid preliminary five-name route).** Naming A,B,T would give
five generators,17682 relators and the index-four Schreier representation,
with tau=16n+1. It is a valid preliminary route, superseded here by Riemann's
observation that the fixed conjugator need not be a basis letter.

**Remark 2 (fixed words do not automatically give polynomial input powers).**
Riemann's counterexample is B0=U0 V0=[5,1;4,1], whose expanding eigenvalue
is 3+sqrt(8)>1. Its powers have exponential growth. A fixed division-free
arithmetic straight-line program in ordinary n computes only polynomials,
so it cannot output those matrix powers for all positive n. This does not
assert that the actual B(x,y) has that matrix or is hyperbolic. Fresh naming
changes the representation of the free presentation group and assigns b
the unipotent V0^3; it does not equate rho(b) and rho(B(x,y)) in that free
group. Their discrepancy is deliberately carried by a relator slot.

**Remark 3 (the old sparse paired cut is not unchanged).** Conjugating by
(T,1) changes each paired letter to (T z T^-1,z). The old table used
conjugator rho(a)=U0 and particular small matrices/supports. Its 198-row
paired-action replacement and subsequent complete sparse counts cannot
be reused with their old coefficients merely because r and m have the
same shape. Relator letters (1,R_j) are unchanged in form, so their first
block remains the identity; exploiting this is a separate credited route
suggested by Riemann. No old full sparse-source claim is made here.

**Question 1 (fixed-data publication).** Root's next materialization task
can choose exact word-composition recipes instead of enormous expanded
strings, but must state and authenticate that representation, its fixed
integer meaning and the complete arithmetic-source bindings. No scientific
execution or new checker is authorized or performed by this proof note.

**Remark 4 (review-status correction).** The first draft listed centralizer
prefix authentication as future work. Root's complete independent branch
audit is already committed at ae670eb58ac7ce9c4816df3cb83e171ce450cba1.
The remaining task is to bind that authenticated prefix into the new
recipes. This note subsequently read the full 88-line audit report; it
does not claim to have performed its literal record comparison.

Evidence is hand group/matrix algebra and inert established-document reads.
No supplied/frozen helper, presentation expander, coefficient evaluator,
scientific array, degree propagation or build was executed. Primary
Accepted action/embedding premises and generic native-history theorems
remain imported within their already declared scope. Root and Riemann
independently read the complete 248-line mathematical draft and passed its
group proof, coefficient bound, loader and generic ledger. Riemann also
reread weighted-mass lines1--130, dense-compiler lines1--126 and projective
lines1--130; he performed no array or coefficient evaluation. Root requested
only the status correction retained in Remark4. The note and exact
byte/read-scope receipt are frozen after that correction and provenance
update; no mathematical construction changed during review.
