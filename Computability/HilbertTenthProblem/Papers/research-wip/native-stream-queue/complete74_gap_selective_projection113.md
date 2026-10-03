# A complete 113-operation universal SOS of exact degree28

The [literal source](complete74_gap_selective_projection113.py) emits a complete universal polynomial evaluable in **113=53M+60A operations**, with **24 strictly positive existential witnesses** and exact degree **28**. It has the same ordinary positive input and fixed admissible compiler numerals as the [complete74 comparison construction](complete74_factored_first_norm.md). Computation duration remains existential and unbounded. This is a degree tradeoff: the separate achieved bounds of74 comparison operations and86 operations for one universal polynomial remain unchanged.

The change supplies the positive first-root gap instead of the ordinary first root, then erases six existing positive graph coordinates while retaining the supplied main parameter a and ratio ordinate c. The [receipt](complete74_gap_selective_projection113.json) contains this complete source and every member of a finite256-source family. No program decoder, equation, ratio condition, input operation or finalizer is free or omitted.

## 1. Exact first-root change in the actual raw source

Start from the frozen `raw30` packet of complete74, with30 positive witnesses and19 comparisons. Its actual paid definitions are

    X=w*q³, Y=s*q³, E=XY, kY=k*Y, L=E*(kY)=XY²k.

Here k is the **independent supplied raw witness**. It is not identified with eta+zeta until the corresponding positive definition is selected below. The actual first comparison is

    L(L+k)=tau²−1.                                  (1)

This is the ordinary root equation, not the native half-root equation with right side `tau*(tau+1)`.

Replace tau by a supplied positive gap g, called `tau_gap`, with proof maps

    tau=L+g,             g=tau−L.                   (2)

The source evaluates (1) in the equivalent comparison form

    1−g²=L*(2g−k).                                  (3)

On every integer or rational tuple, including tuples where the comparisons fail,

    L(L+k)−((L+g)²−1) = 1−g²−L*(2g−k).             (4)

No runtime gate reconstructs tau: (2) is a witness map. The first-root block changes from five operations to six:

    L=E*(kY), two_g=g+g, signed_gap=two_g−k,
    cross=L*signed_gap, g_square=g*g, rhs=1−g_square.

It still costs3M, and now costs3A. The current source names `L9` and `R9` contain cross and rhs respectively; the current comparison is `R9=L9`. Their historical meanings are not active interface claims. The old `first_next` has no consumer outside the old first coefficient, and tau has no consumer outside its square. Every other raw source definition and comparison is unaffected by this coordinate change.

For any positive new tuple, L>0 and tau=L+g>0 before testing an equation. Conversely, at a positive old zero of (1),

    tau²−L²=Lk+1>0.

Since tau and L are positive, tau>L; hence g=tau−L is a strictly positive integer. This proves the inverse positivity directly, before applying any parent universal theorem or recovering typed masks, indices or Pell signs. The inverse does not preserve arbitrary positive off-zero tuples. The public projection rejects a nonpositive gap; its explicitly signed algebra mode retains the unrestricted integer coordinate identity.

Thus the gap change is a bijection of the full positive zero sets, preserving every other supplied coordinate and fixed input. It is the reverse direction of the root tradeoff underlying [complete86](complete86_factored_first_root.md), but at the actual symmetric-scale raw comparison source. The first comparison is retained exactly; no unit-sign argument or parity-normalized weakening is introduced.

## 2. The selected six positive definitions

The default emitted circuit removes precisely q,C,k,d,kappa,mu, through the already established positive triangular definitions:

    q=(B−1)Jrep+1,       C=Z+W,       k=eta+zeta,
    d=X+a*c+ga*H,        H=4a+3,       Delta=a²+H,
    u=twice_cell_bits*x+inner_bits,
    kappa=u+delta*Delta,
    mu=W+a*kappa+rho*H.                              (5)

The current source register named `A` contains Delta. The witnesses a and c remain independently supplied. Their equations

    a=E+Y,              c=kY+eta

are still explicit retained comparisons. Removing a or c can raise degrees elsewhere, which is why the lowest-degree choice keeps them.

Every expression in (5) is positive on the entire retained positive grid: B−1>0, Jrep>0, H>0, Delta>0, the fixed input numerals are positive, and all named summands and factors are positive. This positivity holds independently of the retained comparisons. The dependency order is acyclic, and tau is finally restored by (2), whose L uses the actual selected k.

The24 retained witnesses, in the emitted order, are

    F,Jrep,W,Z,a,alpha,c,delta,eta,f,ga,h,i,j,o,phi,r,
    rho,s,tau_gap,w,y_aux,zeta,zquot.

There remain13 comparisons, at original indices

    1,2,3,5,6,8,9,11,12,13,14,16,17.

The source records every retained/deleted index and the exact current register restoring each deleted coordinate. In particular, no old comparison index is silently reused for a different equation. At index5, equation (4) preserves the old residual itself, despite reversing the displayed operand names.

Given a positive old zero, erase the selected graph coordinates and replace tau by g. The deleted equations force exactly (5), and the remaining13 residuals vanish by (4) and ordinary substitution. Conversely, start from a positive child zero. Restore (5) and then tau=L+g. All restored coordinates are positive before using the parent theorem; the deleted equations hold identically, and every retained old residual agrees with the current residual. The two maps are inverse on the complete positive zero sets.

More strongly, for any integer child tuple v, let restore(v) denote these polynomial definitions, without positivity restrictions. The full raw parent sum of19 squares satisfies

    SOS_raw74(restore(v)) = SOS_new(v).              (6)

The six deleted residuals are identically zero on the restoration graph. Identity (4) handles the changed first residual; the other retained residuals are exact expression-DAG identities. This is equality after the specified coordinate restoration, not equality at identically named supplied tuples. The same graph identity holds over the rationals and every commutative ring. Its universal interpretation retains positive integer witnesses.

The program ports remain `Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF`, with the complete74 compiler meanings and restrictions, including its shifted MF convention. The arithmetic APIs do not certify that arbitrary positive values at these ports describe a valid compiled program. Neither the input language nor the fixed-numeral recipe changes.

## 3. Complete counts and exact degree

The raw gap certificate costs75=40M+35A. Each positive graph elimination aliases an already paid definition and removes one comparison. Eliminating q replaces the old paid `q−1` by the paid `repunit+1`, while all consumers of q−1 use the already paid repunit. A topological traversal emits each needed gate once. None of these eliminations changes the75-operation certificate cost.

For e retained comparisons, the explicit SOS finalizer pays e residual subtractions, e squares and e−1 additions. The default has e=13, so

    75+13+13+12=113=53M+60A.

All75 certificate gates reach comparison outputs, and all113 polynomial gates reach the sole output. All24 witnesses, the ordinary input and all six fixed numeral ports occur. Every binary multiplication by a numeral is charged. There are no residual witnesses or additional hidden equalities.

With x and each retained witness given degree one and compiler numerals fixed, the13 residual degrees are bounded by

    1,5,4,14,5,9,8,8,6,10,2,3,7.                   (7)

The two graph-defined root norms have genuine polynomial cancellations. In the main norm put v=X+ga*H and z=c; in the input norm put v=W+rho*H and z=kappa. Both use the all-value identity

    (a*z+v)²−(a²+H)*z²−1
      = v²+2*a*z*v−H*z²−1.                         (8)

No residual is set to zero to reduce the formal degree. The main residual has degree at most8 and the input residual degree at most7 after (8).

Only the first residual reaches degree14. Put b=B−1 and retain g for `tau_gap`. Its highest homogeneous part is

    −b^9*w*s²*(eta+zeta)*Jrep^9*(2g−eta−zeta).

Thus the complete SOS has highest homogeneous part

    b^18*w²*s^4*(eta+zeta)²*Jrep^18*(2g−eta−zeta)².  (9)

This is a nonzero polynomial for every admissible fixed b>0. No other square reaches degree28, so (9) proves exact degree28 uniformly over all fixed program slices. It is not a syntactic degree estimate, a degree modulo the equations, or merely a witness at one chosen program.

The unprojected gap source costs131 operations with30 witnesses at the same exact degree28. Applying all eight positive definitions costs107 operations with22 witnesses but raises the exact degree to84. The selected six balance these two effects.

## 4. The precise finite family and its frontier

The emitter considers all256 subsets of the eight established positive definitions

    q,C,k,a,c,d,kappa,mu.

The additional two available definitions are a=E+Y and c=kY+eta. Every subset remains triangular and unconditionally positive. If n definitions are selected, the complete source has30−n witnesses,19−n comparisons,75 certificate operations, and131−3n polynomial operations. The receipt contains all256 complete source/finalizer packets, with their graph proofs and uniform degree certificates.

For every member, the degree checker first derives upper bounds from the actual source, using only the two literal cancellations (8) when their root coordinate is selected. It propagates dependencies of the highest homogeneous coefficients on fixed compiler numerals. Every residual attaining the maximum is proved independent of all fixed numerals except Bm1. It then executes the actual source in the exact polynomial ring Q[t,Bm1], substituting t for each input/witness and3t for g. At least one maximal residual has a nonzero t-leading coefficient polynomial in Bm1 whose coefficients all have one sign. That coefficient cannot vanish at any Bm1>0. Combined with the proved upper bound and the sum of squares, this proves every recorded exact degree uniformly; two isolated fixed-base specializations are not being substituted for that proof.

The operation/degree frontier inside this precisely stated family is:

|Operations|Exact degree|Witnesses|Equations|Selected definitions|
|---:|---:|---:|---:|---|
|113|28|24|13|q,C,k,d,kappa,mu|
|110|68|23|12|q,C,k,c,d,kappa,mu|
|110|68|23|12|q,C,k,a,c,d,mu|
|107|84|22|11|all eight|

The two110/68 rows are distinct sources with the same objective values. Only113/28 extends the authenticated [existing finite operation/degree frontier](complete86_first_root_partitions.md). The other new family points are dominated there. The resulting combined catalogue is

    86/179,87/135,88/123,89/113,90/109,91/102,92/80,
    93/72,94/62,95/54,96/50,97/48,98/44,113/28.

The earlier points use19 positive witnesses; the new degree28 point uses24. This is an achieved tradeoff, not a claim that24 witnesses, degree28 or113 operations is optimal in general. The census does not enumerate other positive definitions, signed projections, new norm coordinates, asymmetric scale theorems, different finalizers or alternative computational substrates.

## 5. Guards, replay and evidence

The implementation authenticates nine parent source/receipt/proof files before reading their JSON. It executes no historical Python code and has no shared mutable canonical cache. `canonical_parent(root=...)` returns the exact frozen raw30 packet. `build(eliminated=DEFAULT,root=...)` accepts an exact ordered tuple naming one of the256 subsets. `rewrite(parent,...)` additionally requires recursive exact-type equality with the entire selected raw parent. No partially matching local fragment is accepted.

`checked`, `polynomial_source`, `evaluate` and `degree_certificate` authenticate the complete current packet before use. Boolean/float aliases of integer coefficients and metadata are rejected. Public evaluation requires exactly the full coordinate dictionary and exact integer values. Its default requires positive input, witnesses and numeral ports; the explicitly Boolean signed option is only an algebraic evaluation mode.

`restore_assignment` computes the deleted fields and old tau, preserving positivity for every positive child tuple. `project_assignment` requires the selected definition graph, and in positive mode also requires the recovered gap to be positive. Every old positive zero meets both conditions by the proof above. Signed graph maps work on all integer tuples on that graph. Rational identity checks use a separate internal evaluator and do not relax the public integer-domain contract.

Run with Python3's standard library:

```sh
python3 complete74_gap_selective_projection113.py \
  --root /path/to/native-stream-queue \
  --expect complete74_gap_selective_projection113.json
```

`--output PATH` writes the deterministic receipt. Optimized execution under `-O` is rejected. All Markdown and source parent bytes remain unchanged.

The receipt records256 complete source/degree certificates and4864 exact old-comparison graph identities;2048 full numerical graph identities, including1024 signed and256 rational cases;38912 residual-value checks;1024 unconditional positive restorations; ten public graph roundtrips and ten public evaluations on representative forms;288 malformed-caller rejections;21 defensive-copy checks; nine warm parent-pin rejections; and an optimized-mode rejection. It also contains72 exact positive first-norm Pell components. Those components are not full accepting compiled-program witnesses. The universal theorem follows from the quantified positive-zero bijection with the authenticated parent, not from finite examples.

Author writer and fresh read-only receipt replay pass. No archived report, existing source or repository file is modified by this packet.
