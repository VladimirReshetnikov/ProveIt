# Four complete linear-input auxiliary quotient polynomials

The four constructions below retain the ordinary positive input and full fixed-program recipe of their actual saved parents. Each has **18 strictly positive witnesses** and a complete seven-factor product-minus-one output. All numerical multiplications, squares, subtractions and finalizer gates are paid.

| First coordinate | Auxiliary coordinate | Operations | M | A | Exact degree |
| --- | --- | ---: | ---: | ---: | ---: |
| root | ordinate | 87 | 47 | 40 | 119 |
| root | positive gap | 88 | 47 | 41 | 113 |
| positive gap | ordinate | 88 | 47 | 41 | 109 |
| positive gap | positive gap | 89 | 47 | 42 | 103 |

The 88/113 form is retained as a complete source although 88/109 dominates its operation/degree pair. These extend the 18-witness cost/degree tradeoffs; they do not reduce the separate 85-operation bound. This is a four-source construction, not a search over all circuits or a new grouping census.

The [helper](complete_linear_auxiliary_quotient_family.py) reads only pinned JSON and proof bytes; it imports or executes no predecessor Python. Its [receipt](complete_linear_auxiliary_quotient_family.json) contains every instruction of all four outputs. The helper is a bounded research CLI, with no maintained public packet API promise.

## 1. Exact parents and definitions

Select forms 3,8,16,21 of [the saved transport-shear census](transport_shear_partition_census.json), in each case its literal one-block, anchor-zero winner. These are respectively the first-root linear-coupled, first-root auxiliary-gap-coupled, first-gap linear-coupled and first-gap auxiliary-gap-coupled eight-unit sources. Their costs/degrees are 88/122,89/118,89/112,90/108, with 19 positive witnesses. The source guards the exact factor list, full finalizer, linear input modulus, asymmetric scales and ordinary strong equation.

Retain the entire valid fixed compiler recipe, including synchronization, masks, marker and input conditions from [linear-input89](complete75_linear_input_modulus89.md), its [asymmetric extension](complete75_asymmetric_linear_gap_tradeoffs.md), the [first-root transfer](complete86_first_root_partitions.md), and [transport shear](complete86_transport_quotient_shear.md). The six fixed numeral ports are `Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF`. They are not arbitrary positive constants: the paid MF is the shifted mask MF0+B−1, B=Bm1+1 is the required power of two at least16, and all other inherited compiler conditions still apply.

Use the notation

    q=(B−1)J+1, X=wq, Y=sq³, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    A=a+2, Delta=A²−1, H=4a+3,
    D=X+ac+(rho+sigma)H,
    C=q−F−Z−alpha−2dx, W=C−Z, u=2dx+b,
    kappa=u+delta*(a+1), mu=W+a*kappa+rho*H,
    R=(q²−Z−qF)(q²−1)+(MC+q(MF0+B−1))J,
    K=k−hE, S=ic², Kaux=Delta(f²−1).

The register named `A` stores Delta, not mathematical A. Registers `R10a,R10b,UM,R12,r_lhs,index_difference` store c,k,E,a,R,K. The first factor is either

    N0=tau²−L(L+k), L=XY²k,

or, with supplied positive g,

    N0=g²+L(2g−k), tau=L+g.

The ordinary strong factor is Ns=1+S²−Kaux. Replace the two supplied coordinates o,j by one positive T=`auxiliary_quotient`, retaining every other supplied coordinate, and compute

    V=c(Tf−1)−Rf².

If the auxiliary coordinate is its positive gap e, compute y=V+e; otherwise y is supplied positive. The other factors are

    Nm=D²−Delta*c², Ni=mu²−Delta*kappa²,
    Na=Kaux*(V²−y²)+y²,
    Nk=K−R,
    Nt=(Kconstant+w)*C+(q−F)−transport_quotient*(q−1).

The complete output is F=N0*Nm*Ni*Na*Nk*Nt*Ns−1. The old omitted factor was Nl=of−c−jc+K.

The new V uses five paid rows Tf,Tf−1,c(Tf−1),Rf²,V, reusing the old f². These replace the old two V rows, three Nl rows, and one final multiplication by Nl. The total multiplication count is unchanged; one addition/subtraction and one supplied witness disappear. R remains fully paid and its new use causes a topological reorder, not an uncharged computation.

## 2. All-value correction, not an off-zero equality

With j independent and o=cT−Rf, the following identities hold over every commutative ring, including c=0:

    of−c=V,
    Nl−Nk=V+R−jc,
    Fparent(o=cT−Rf,j)+1−(Fchild+1)*Nk
       =(Fchild+1)*(V+R−jc).

The same identities hold when the first root or auxiliary ordinate is reconstructed from its gap. For c nonzero over the rationals, j=(V+R)/c gives

    Fparent(restored)+1=(Fchild+1)*Nk.

The division is a coordinate formula, never a child instruction. Off zero j need not be integral, nor o or j positive. In particular the complete parent and child polynomials are not asserted equal under this rational restoration. The positive-zero proof below must restore the sign of Nk before invoking a parent zero theorem.

## 3. Native bounds and ordinary rank before auxiliary positivity

At a positive integer child zero all seven factors are integer units. The consecutive-product negative-Pell descent excludes N0=−1. In the gap case the positive root tau=L+g is available unconditionally, so this argument is exactly the root argument. Since Delta is0 or3 modulo4, Nm and Ni cannot be−1. The ordinary Ns also cannot be−1: if Delta=0 modulo4 it is a square plus1; if Delta=3 it is the sum of two squares. Thus Ns=1 and Kaux=S². Then Na modulo4 is y² or V², even if both y and V were initially signed. It follows that

    N0=Nm=Ni=Na=Ns=1, Nk=epsilon, Nt=nu,
    epsilon=nu in {−1,1}.

No step here uses the input-index modulus Delta rather than a+1, or assumes the auxiliary gap reconstructs a positive ordinate.

The literal sheared transport is

    Nt=(Kconstant+w)C+1−F−(transport_quotient−1)(q−1).

Its final terms are nonpositive and its C coefficient is at least2. Therefore C≥0 and F+Z<q. The unchanged shifted-mask packing gives

    (2q−1)(q²−1)<R<q⁴−q³,
    3q+1<R−2<R+2<q⁴≤E,
    a>R+2, Delta>R>0.

These are pretyping inequalities, not an assumption that q is already dyadic. The first positive norm has fundamental unit 2XY²+1+2sqrt(XY²(XY²+1)), so for P=2XY²+1,

    k=2psi_P(n), n≥1,
    2n=R+epsilon+vE, v≥0, n≥(R−1)/2≥24.

The main root D is positive by its actual source expression, hence D=chi_A(p),c=psi_A(p). Since P>A and c>k, one has p>n. These inequalities give

    c>A*Delta², c>2p, c>2R.

In particular they precede positivity of V, restoration of j, auxiliary Pell classification, and any complete parent zero theorem.

Apply the general middle rank argument of the pinned [ordinary relaxed auxiliary proof](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md#the-relaxed-norm-forces-an-integral-pell-solution-at-a) to S²=Delta(f²−1), S=ic² and c=psi_A(p)>A*Delta². It gives

    f=chi_A(m), S=Delta*psi_A(m), p|m, c|m,
    m≥c>2p.

Strong divisibility then gives c|psi_A(m), hence c²|(f²−1). We do not infer c²|psi_A(m), the stronger normalized divisibility that is unavailable here.

## 4. Recover V, y, o and j without a circular positivity assumption

The ordinary strong equation gives f²=1+i²c⁴/Delta. From the large-c bounds, f²>4c² and f²>Delta+c. Since Delta−R≥1,

    Kaux−Rf²−c=(Delta−R)f²−Delta−c>0.

For any integer H0>1, H0*V²−(H0−1)*y²=1 excludes V=0. If v0=|V|>1, it gives |y|≥v0+1 and thus

    v0²−1≥(H0−1)(2v0+1), so v0≥2H0−1.

Take H0=Kaux. Positive T gives V>−Rf²−c>−Kaux, excluding that large negative branch. The cases V=±1 are excluded by V≡−c modulo f and f>2c,c>2. Consequently V>0. In the auxiliary-gap variants **only now** does e>0 give y=V+e>0. This is why the preceding estimate used |y| rather than assuming y positive.

Restore

    o=cT−Rf=(V+c)/f,
    j=(V+R)/c=Tf−1−R(f²−1)/c.

The first is integral by its polynomial formula; the second by c²|(f²−1). Both are positive. Thus V=of−c=jc−R, and Nl=Nk=epsilon. The old product is epsilon at this stage; its zero theorem is not yet applicable.

## 5. Sign closure and exact positive-zero bijections

Use only the local fixed-minus step-down from the pinned [half-parameter proof](../../1980/HALF_PARAMETER_PELL_92_PROOF.md) and [ordinary86 proof](complete86_ordinary_auxiliary_projection.md#5-fix-the-index-sign-then-transfer-both-directions). Here S=ic², f=chi_A(m),m>2p, and V=of−c=jc−R. Auxiliary Pell classification with now-positive V,y gives SV=chi_S(ell), with ell odd. The polynomial chi_S(ell)/S and S²=Delta(f²−1) imply chi_A(2ell)=chi_A(2p) modulo f. Strict nearest-multiple reduction gives ell=±p modulo m. Reducing the same odd polynomial modulo c gives R=±p modulo c. Since 0<R,p<c/2, p=R.

The first-index congruence above then has v=0: v≥1 would give 2n≥R−1+E>2R, contrary to n<p=R. If epsilon=−1, p=2n+1. Pell duplication, with Q=2A²−1>P, gives

    psi_A(2n)=2A*psi_Q(n)≥2A*psi_P(n)=Ak,
    c=psi_A(2n+1)>Ak>k(Y+1),

contrary to c=kY+eta and k=eta+zeta with positive eta,zeta. Hence epsilon=nu=1. All eight restored parent factors equal1. **Only at this point** invoke the exact selected historical parent's complete fixed-program and ordinary-input theorem. Its smaller input modulus kappa=u+delta*(a+1) is retained literally; the argument above has used Ni only for its norm sign, so that modulus has not been silently replaced.

Conversely, every positive zero of each exact parent has all eight factors1 and the same ordinary rank conclusion. The old index and linear equations give of+R=c(j+1), while f²=1 modulo c. Multiplication by f modulo c shows c|(o+Rf). Thus T=(o+Rf)/c is a positive integer. It reconstructs exactly the old V, retaining the old ordinate or gap as appropriate. Every child factor is1. These formulas recover o,j,T uniquely and leave every other supplied coordinate and the input fixed.

Therefore each child is in bijection with its own complete parent positive integer zero set. No signed-zero, real-zero, positive off-zero, or arbitrary-numeral theorem is claimed. The bijections are not limited to canonical witness extensions.

## 6. Uniform exact degrees

Give every supplied witness and ordinary x degree1, every fixed numeral degree0. Write

    Q0=Bm1*Jrep, k0=eta+zeta, gamma0=rho+sigma,
    C1=Q0−F−Z−alpha−twice_cell_bits*x,
    T2=w*C1−transport_quotient*Q0.

The actual leading forms are:

| Factor | Degree | Leading form |
| --- | ---: | --- |
| First root |22| −w²*k0²*s⁴*Q0¹⁴ |
| First gap |12| w*k0*s²*Q0⁷*(2g−k0) |
| Main |18| 8*gamma0*w²*k0*s³*Q0¹¹ |
| Linear input |20| 4*delta*(2rho−delta)*w³*s³*Q0¹² |
| Auxiliary ordinate |28| w²*k0²*s⁴*Q0¹⁴*T²*f⁴ |
| Auxiliary gap |22| −2*w²*k0*s³*Q0¹¹*T*f³*e |
| Index |7| −h*w*s*Q0⁴ |
| Transport |2| T2 |
| Ordinary strong |22| i²*k0⁴*s⁴*Q0¹² |

The main/input cancellations are the all-value polynomial identity

    (z+ab)²−(a²+H)b²=z²+2abz−Hb²,

with z=X+gamma*H or z=W+rho*H. The auxiliary-gap cancellation is V²−(V+e)²=−e*(2V+e). The helper checks these coefficient identities and the actual source cones before using their leading forms. No zero-only unit substitution enters the degree calculation.

The product of the seven displayed nonzero forms is the entire leading homogeneous form. Their degrees sum to119,113,109,103 in table order. Every form is nonzero for every admissible fixed compiler specialization: Bm1>0; T2 has the otherwise unmatched coefficient−Bm1 of transport_quotient*Jrep; all other factors displayed involve independent supplied coordinates. In particular 2rho−delta and 2g−k0 are not constrained by an equation when computing degree. Subtraction of1 does not alter the product leader. This proves exactness uniformly on every valid fixed-program slice, without specializing supplied witnesses.

## 7. Evidence and replay

The helper authenticates 53 actual predecessor source, receipt and proof hashes on every run. It reads the four exact saved parent source arrays and checks all352 live child gates,332 retained expression identities under the proved V cut, every removed o/j consumer and all eight complete parent/child finalizers. Seven exact sparse-polynomial identities establish the cuts and full correction, including c=0. The four entire homogeneous leading polynomials have240,216,456,408 nonzero monomials respectively; every coefficient is saved in the receipt with all six fixed numeral symbols kept symbolic.

Supplemental evaluations check160 complete ring corrections, including64 rational cases and9 cases with c=0,1,120 retained factor values and151 rational restorations with c nonzero. The auxiliary-gap cases include55 negative computed-y algebra fixtures. These are not claimed as complete positive zeros, counterexamples, or proof substitutes. Residue checks cover256 ordinary strong and64 signed auxiliary classes.

The elementary sparse-polynomial and leading-form utilities are adapted from the ordinary86 author helper; that reuse is disclosed and is not presented as independent review. No previous verifier, builder or full census executes. The proof in Sections3–5 supplies the unbounded assertions that these finite algebra checks do not.

Taking the union only with the saved [18-witness partition frontier](complete_auxiliary_unit_partition_frontier.md) gives

    85/175,86/131,87/119,88/109,89/103,91/80,93/64.

The four complete sources are established before this metadata comparison. No additional groupings are enumerated here, and the finite union is not an optimality claim over other representations.

Run from any directory, with Python's standard library:

    python3 /absolute/path/complete_linear_auxiliary_quotient_family.py \
      --root /absolute/path/native-stream-queue \
      --expect /absolute/path/complete_linear_auxiliary_quotient_family.json

The writer and fresh normal and optimized (`-O`) exact saved-receipt replays from `/` passed. The checks use explicit exceptions, so optimization does not disable them. The receipt recursively compares exact JSON types. All note targets resolve against the intended installation directory; no frozen predecessor bytes were changed.
