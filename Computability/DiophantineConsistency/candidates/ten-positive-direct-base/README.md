# Ten positive unknowns,107 operations,degree340

This complete sibling retains ten positive unknowns and lowers exact
degree from368 to340 at six extra operations. The full evaluator has64
multiplications,25 additions and18 subtractions, with every107 gate,
ten inputs and four fixed ports live. It is a separate cost/degree
tradeoff against101/368, not a universal improvement. All accepted
endpoints, canonical pages, common documents and Lean files stay unchanged.

The new independent coordinate x replaces w, with X=q+x. Put

    B=(q*K0+X)*C-qF,
    W=1+q(q-1)L, P=q^4(q-1), M=P*mu^2*H,
    Z=P*mu^2*[H(n+V)+Kpos]
         +H[mu^2*(q(q-1)Y-q^3WB-(q-1)X)-P*e].

Every other kernel and the(3*tau,f,y) octic norm are retained. The only
unknowns are J,F,alpha,i,T,x,Y,n,eta,zeta, all strictly positive.
`equation.json` gives every arithmetic gate, with no variable exponent,
radical or division in its evaluation. The complete original compact44
coefficient tuple is copied under `coefficients/`, with raw and compressed
hashes. No port is replaced independently or left as an existential
coefficient parameter.

## The required order of arithmetic recovery

The proof-only center contains a new -X/q^4 term:

    Z/M=n+V+Kpos/H+Y/q^3-WB/[q(q-1)]-X/q^4-e/mu^2.

The existing modulus separation first recovers integral roots. Main
folding and the first Pell norm give the old large c bounds. The margin
in3*tau+f<HI also absorbs X/q^4, and the larger W makes B<0 contradict
n>0. This recovers C>0 and3q<R<q^4-2. Rank recovery forces q even
before the single coprime modulus mu^2 is separated from the common
q^4(q-1)H denominator. No pairwise coprimality of q,q^3,q^4 is assumed.

The first index and ratio bounds follow in the retained order. An
explicit enlarged whole-product estimate is valid at r>=35, below the
actual r>=48. It recovers X=2^R and then H|Kpos directly. **Only after
this H denominator is removed** does the remaining integer center imply
q|X by reduction modulo q. Thus q is a power of2 and R>3q makes q^4|X.
The new X/q^4 term is now integral. Setting the recovered positive
integer w=X/q gives B=q*Bt; the old Y/q^3 and Bt/(q-1) CRT and fresh
positive source61 reconstruction finish soundness, including J=1.

Completeness from an old zero uses

    x=X_old-q>0,
    n_new=n_old+(W_new-W_old)*t+u,
    (q-1)t=Bt, q^4u=X_old.

The old soundness theorem supplies these integer quotients, t>=0,u>0,
and L>0, so the new n is positive. All Pell kernels stay identical,
M_new=q*M_old,Z_new=q*Z_old, and the new output is q^8 times the old.
There is no assumed positive pointwise inverse map.

The universal licensed carrier identity is

    Z_new-q*Z_old
      =H*mu^2*[q^4*DeltaW*((q-1)t-Bt)+(q-1)*(q^4u-X)],
    DeltaW=W_new-W_old,

under x=X_old-q,n_new=n_old+DeltaW*t+u. It is a complete free-ring
identity with explicit quotient licenses, not a map using undefined
integer division. The separate root-authored ordinary peer verifies this
identity over14 formal variables, its mod-q remainder, B=q*Bt, and the
complete weighted-norm q^8 homogeneity. Its proof/script/normal/optimized
receipts are copied and content-pinned in `source/`.

## Exact degree and complete independent checking

The direct X coordinate reduces A to degree4, Q to26,V to22 and the
unique transport term of Z0=Z-MV to24. The centered omega has degree85;
its fourth power uniquely leads at340. The selected exact coefficient is

    [J^156*x^40*i^20*Y^76*eta^40*alpha^4*F^4]P=2^28*beta^156>0.

The highest x-degree component excludes every K0-dependent leading term;
the other two mask ports also cannot cancel this coefficient.

`CUTS.json` and the independent `check.py` account for every101 parent
row, every operand change and all six inserted definitions. They verify
full topology/liveness, operation inventory, all35 independent weighted
norm coefficients, the primitive mod-q remainder, B/W identities, the
complete licensed carrier cut, q^8 norm homogeneity, and the exact
centered leading component. The leading product is multiplied over eight
formal variables including K0; highest-x extraction proves the selected
coefficient independently. All source dependencies and the whole frozen
parent manifest are checked byte for byte.

Supplementary transcription controls cover120 complete actual-port
kernel/center/output transformations, nine exact unrestricted integer
transformations, two whole actual-tuple degree340 lines and four rejected
semantic corruptions. These finite controls do not replace the unbounded
proof. All four normal/optimized builder/checker runs pass.

The coherent BFS tuple remains a separately calibrated specialization
through the inherited coefficient-uniform native/source theorem; its
different K0 is not identified with the original coefficient here. This
packet supplies an ordinary positive-solvability/refutation equivalence,
not a new Lean or encoded object-ZFC derivation, a proof of consistency,
an optimality claim or a page update. Lean remains paused.

Run from the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/build_ten_positive_direct_base.py --check
python -B -O Computability/DiophantineConsistency/tools/build_ten_positive_direct_base.py --check
python -B Computability/DiophantineConsistency/candidates/ten-positive-direct-base/check.py
python -B -O Computability/DiophantineConsistency/candidates/ten-positive-direct-base/check.py
```

No historical native emitter or Lean process is executed.
