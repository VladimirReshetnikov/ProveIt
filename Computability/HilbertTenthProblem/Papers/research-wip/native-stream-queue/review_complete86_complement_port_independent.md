# Independent challenge of the complement-port obstruction

**PASS.** The frozen [construction and proof](review_complete86_complement_port_math.md) establishes positive zeros of the literal complement-port85 expression for every positive input, on every valid fixed compiler slice. Its inverse coordinate `F=q−u` is negative. Thus this particular one-addition deletion does not supply an85-operation universal replacement. The established [complete86 polynomial](complete86_factored_first_root.md) remains unchanged.

This review independently checked the source, all parameter choices, the unbounded canonical converse, and positivity/integrality of all nineteen supplied coordinates. No flaw was found. The companion [checker](review_complete86_complement_port_independent.py) and [receipt](review_complete86_complement_port_independent.json) pin the author's complete trio and eight actual predecessor source/proof artifacts. The author source is `5bf5183c2e78826e42a836cc035cb0e126cf3fb450749f89282997d8dfc972e8`, receipt `0b09bf02264908d760c163b11f03cfe6f671a6fd320926df6543cd82c271a2a6`, and proof note `f0cba6a4ad0b1f5488782ae943ac0da547a5903401c2f9a332db3a2fcf7df0b3`.

## Literal circuit and fixed parameters

The actual normalized parent has one consumer of F: `q_minus_F=q−F`. Removing that row and replacing its consumers by a supplied positive u gives exactly85 live gates,48M+37A, with nineteen supplied coordinates. The review independently reconstructs every row and verifies each of the eight whole factor formulas and the final product-minus-one. The exact signed graph identity is the sole affine substitution `F=q−u`; it does not itself prove positive-domain equivalence.

The actual scale ports are `X=wq` and `Y=sq³`. The review checks these literal definitions, the two ratio coordinates, the shared `rho+sigma` main quotient, and the affine ordinary-input index. No raw versus projected scale is interchanged. All fixed compiler numerals, including K, masks, cell size d and input offset b, remain fixed throughout the construction.

## Outer construction and population bound

Let `ell=2dx`, `e=ell+b`, and choose `L>=max(d,e+1,4)`, `t=L!`, `q=2^t`. Since d divides t, the required positive integer `J=(q−1)/(2^d−1)` exists. For each odd prime power `p^v|t`, both `p^(v−1)` and `p−1` divide t and are coprime; hence their product divides t. Euler's elementary order bound yields `2^t=1 mod p^v`. The two-part of t divides `2^t`. Therefore `t|q(q−1)`, and in particular `t|A0=q(q²−1)`. This is a proof for every selected factorial, not an inference from sampled widths.

The actual shifted mask remainder

```
T'=MC*J+1+q*(MF0*J−1)
```

satisfies `0<T'<q²−1` and `T'=3 mod4`, using the unchanged mask bounds and congruences. Put `Z=1`, `W=2^e`, `C=W+1`, and `v=2^(T' mod t)`. Selecting

```
u0 = 1−(K+v)C modulo q−1,
u  = u0+(q−1)(2^(8t+8)−1)
```

has no circular dependence: `R=A0*u+T'` always has the same residue `T' mod t`, so `X=2^R` always has residue v modulo q−1. Thus `(K+X)C+u−1` is divisible by q−1 without changing K.

Write `H0=8t+8`, `M=A0(q−1)` and `beta=M−A0*u0−T'`. The bounds `0<=u0<=q−2` give `0<beta<M<2^(4t)`. Consequently

```
R=M*2^H0−beta
 =(M−1)*2^H0+(2^H0−beta),
pc(R)=pc(M−1)+H0−pc(beta−1)>3t+2.
```

The two summands occupy disjoint binary blocks. The lower block is the H0-bit complement of beta−1; no carry assumption is omitted. Also `R=3 mod4`, `R>max(e,3t,15)`, and the chosen u exceeds both q and `W+ell+2`. Therefore

```
alpha=u−W−ell−2,
zplus=((K+2^R)C+u−1)/(q−1)
```

are positive integers, the literal transport factor is one, and the restored parent F is negative.

## Direct converse without a forbidden bound transfer

The earlier half-binomial theorem includes an upper bound on R for its soundness direction. The obstruction does not apply that theorem beyond its hypotheses. It uses its explicit construction, whose sufficient inequalities can be proved afresh at the chosen large R.

Let `r=(R−1)/2`, `X=2^R`, and let `2Y` be the integer part of `(X+1)^(2r)/X^r`. The binomial expansion gives an even integer part and a strictly positive discarded tail below1/4. Its leading integer term gives `Y>=X^r/2`. The exact central-binomial valuation is

```
v2(Y)=pc(r)−1=pc(R)−2>=3t.
```

All other integer-part terms are divisible by X, with strictly larger two-adic valuation. Hence `s=Y/q³` and the actual asymmetric `w=X/q` are positive integers.

Set `a=Y(X+1)`, `A=a+2`, `Delta=A²−1`, `P=2XY²+1`, `c=psi_A(R)`, and `k=2psi_P(r+1)`. The ratio bounds in the pinned base-two and half-binomial proofs apply directly to these selected indices. Their hypotheses here follow from `a>8r` and `6XY²>a`, both immediate from the explicit large X,Y. They give

```
0 < c/k − (X+1)^(2r)/(2X^r) < 16r/(X+1) < 1/2.
```

Combining the strict lower bound with the discarded tail below1/4 yields `Y<c/k<Y+1`. Thus `eta=c−kY` and `zeta=k−eta` are positive integers. The congruence `P=1 mod E`, `E=XY`, gives the integer `h=(k−R−1)/E`, and strict Pell growth makes it positive. `tau_root=chi_P(r+1)` satisfies the exact paid first norm `tau_root²−(XY²k)(XY²k+k)=1`.

None of these steps recovers indices from an arbitrary zero or assumes the old packed-field upper bound. They construct the indices first and verify the sufficient inequalities directly.

## Auxiliary congruences and shared input quotient

For the normalized strong block choose

```
m=2cR, f=chi_A(m), i=psi_A(m)/c²,
T=Delta*psi_A(m), y_aux=psi_T(R), V=chi_T(R)/T.
```

The expansion `(chi_A(R)+c*sqrt(Delta))^(2c)` proves `c²|psi_A(m)`: its linear square-root term contains `2c²`, and every remaining odd term contains at least `c³`. Thus i is a positive integer. Since R is odd, `chi_T(R)/T` is an integer polynomial in T².

There is a self-contained general proof of both required minus congruences. Put

```
G_r(z)=chi_T(2r+1)/T, with z=T².
```

It has initial polynomials `G_0=1`, `G_1=4z−3` and recurrence `G_(r+1)=(4z−2)G_r−G_(r−1)`. The odd subsequence `psi_A(2r+1)` has initial polynomials1 and `4A²−1`, and recurrence coefficient `4A²−2`. Therefore, by induction,

```
G_r(1−A²)=(-1)^r*psi_A(2r+1),
G_r(0)=(-1)^r*(2r+1).
```

Here r is odd because `R=3 mod4`. The Pell identity gives `T²=Delta*(f²−1)=1−A² mod f`, while c divides T. Hence `V=−c mod f` and `V=−R mod c`. This proves that `o=(V+c)/f` and `j=(V+R)/c` are positive integers, independently of any old bound on R. The two normalized auxiliary/strong factors are one, and `V=of−c=jc−R` gives the coupled linear factor one once `k=R+1+hE` is used.

For the ordinary input use `kappa=psi_A(e)`, `mu=chi_A(e)` and `delta=(kappa−e)/Delta`. Since e is odd, the recurrence gives `psi_A(e)=e mod Delta`; since e>=3, strict growth gives delta>0. The exact sequence

```
gamma_n=(chi_A(n)−a*psi_A(n)−2^n)/(4a+3)
```

has integer initial values `gamma_0=gamma_1=0` and recurrence

```
gamma_(n+1)=2A*gamma_n−gamma_(n−1)+2^(n−1).
```

It is positive and strictly increasing from n=2. Thus `rho=gamma_e>0` and `sigma=gamma_R−gamma_e>0` because R>e. This verifies the actual shared main/input quotient interface; it does not replace sigma by an independent main quotient.

The nineteen coordinates are now explicitly covered: J,u,alpha,zplus and Z by the outer construction; w,s by valuations; tau_root,eta,zeta,h by the first/main construction; f,i,j,o,y_aux by the auxiliary construction; and delta,rho,sigma by the input sequence. All eight literal factors equal one. For a fixed compiler of a proper input language, the changed source consequently accepts inputs outside that language. This is stronger than merely observing that a proposed inverse map can be negative off zero.

## Executable evidence and limits

The independent helper imports no author code. It authenticates eleven artifacts, reconstructs the entire85-gate source, verifies its closure/liveness and all eight factor formulas, and checks the complete finalizer. Additional exact evidence consists of eleven factorial-modulus cases,78 outer cases spanning different admissible mask pairs and K values, five first/main/input constructions, thirteen symbolic odd-index polynomial instances, and seven separate canonical auxiliary cases. These fixtures do not purport to materialize the enormous full auxiliary tower at a valid outer width. The all-parameter proof above, not those finite tests, establishes the full positive-zero counterfamily.

All predecessor bounds and scopes were read directly from the pinned proof notes. The claim is specific to deleting F by this complement coordinate; it is not a lower bound excluding other85-operation universal polynomials. The separate exact-affine scout's finite86 minimum remains correctly scoped and unchanged.

Only the standard library is required:

```sh
python3 review_complete86_complement_port_independent.py \
  --root /path/to/native-stream-queue --artifacts /path/to/author-trio \
  --expect review_complete86_complement_port_independent.json
```

`--output FILE` writes a fresh receipt. Writer and fresh replay from `/` passed. No repository file or Git state was modified.
