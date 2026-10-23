# Nine variables with support-selective positive-digit coding

This construction is pinned to ProveIt commit
`124c07c0b77a9e20e84676514d8b1ff78536ea3f`. Its parent is the coherent
package-31 quadratic system, in the supplied unshifted raw records. The
numerical Jones ratio bridge and the two-square finalizer are the same as
package 45, `nine/MULTITARGET_NINE_PROOF.md`, preserved in `upstream/`.
The new part is the source: selective rather than full Sidon isolation,
nonuniform target spacing, and moving positivity shifts into a single common
convolution factor. All coefficients and all powers are fixed integers.

For the supplied layout, there are nine strictly positive unknowns, degree
**19,615,180**, and **606** binary arithmetic operations. The equivalent
nonnegative-domain version uses **609** operations. The generated degree
certificate is an equal polynomial with its decisive cancellation resolved;
its operation count is not the advertised primary count. No global minimum
or new end-to-end Lean certificate is claimed.

## 1. Fixed source and finite separation certificate

Let `p_1,...,p_22` be the unshifted quadratic residuals in 31 variables of the
package-31 parent. The eighth original residual is negated, which does not
change its zero set, and it is assigned the final target. The precise raw-row
order, signs, four-port coefficient recipes, subsequent target permutation,
and 94 weighted monomial records are in `data/raw_recipes.json` and
`data/layout.json`. The four ports are the whole package-31 tuple with the
shifted MF convention, preserved as bytes under `coefficients/payloads/`.

Write `w_0=0,w_1,...,w_31` for the weights, `W=max w_i`, and let `h_j` be
the target of row `p_j` in target order. Here `W=175`, `h_1=246`,
`h_22=5148`, and `K=h_22+2W=5498`. All positive weights are distinct.
There are 528 unordered pairs, allowing repetition, among indices 0,...,31.
Only 62 pairs occur in the padded supports of the actual residuals.

For a degree-at-most-two multi-index alpha, append `2-|alpha|` copies of
index 0 and call its weight sum `s_alpha`. The finite certificate states:

* Whenever alpha occurs in a residual, its pair weight `s_alpha` is attained
  by exactly that padded pair among all 528 possible pairs.
* If alpha occurs in row k, then `h_j-h_k+s_alpha` is a possible pair sum
  precisely when j=k; in that case the only corresponding pair is alpha.

The second item excludes all cross-row interference. The verifier exhausts
the entire finite family; it does not assume a full Sidon property, which
these weights do not have. It also checks that the 94 exponents below are
distinct, nonnegative, and have unique top coefficient 2 at exponent 5148.

For `p_j(X)=sum_alpha p_(j,alpha) X^alpha`, put

`c_(j,alpha)=(2-|alpha|)! product_i(alpha_i!) p_(j,alpha)`

and define

`D(t)=sum_(j,alpha) c_(j,alpha) t^(h_j-s_alpha)`.

For arbitrary integers x_i, put `C_x(t)=(1+sum_i x_i t^w_i)^2`. The
finite separation certificate and the multinomial coefficients prove

`[t^h_j] C_x(t)D(t)=2p_j(x_1,...,x_31)`.

This identity is the only isolation requirement. Unused pair sums may
collide freely. It is the reason a range of 175 replaces the old range 799.

Every weighted coefficient has port degree at most two and coefficient
L1 norm at most eight. Thus its absolute value is at most
`H=8(1+beta+K0+MC+MF)^2`. The supplied fixed tuple has all four ports
strictly below `2^1070004`, whence `H<2^2140017`. Set

`M=2^2140017`, `b_floor=2^2140030=8192M`.

These are explicit integers, and `b_floor` is also the source-base numeral
used by the companion ten-integer construction. D's unique top coefficient
is 2; all others have absolute value less than M.

## 2. Nine-variable source with one shared positivity shift

First use epsilon, phi, n >= 0 and g,h,s,w,i,j > 0. Define ordinary
polynomial registers

```
b = b_floor + epsilon,       B = b^3,
ell = sum_(r=1)^31 B^w_r,    Dcode = D(B),
N0 = B^(W+1),               N1 = 4 B^(K+1),        N = N0 N1,
Mask = N0-1-(b-1)ell,
Targets = sum_(r=1)^22 B^h_r,
Tcode = Mask+(B-2)Targets N0,
Jcode = 2(1+ell+g)^2 Dcode + B sum_(r=0)^K B^r,
Scode = g+Jcode N0,
R = (N-1)[(Scode+Tcode+1)N+Tcode+1],
Gcap = 32b B^W.
```

The term `ell` in `1+ell+g` is essential. The mask will encode nonnegative
digits z_i in g, while the convolution then evaluates the unshifted parent
at the positive digits `x_i=z_i+1`. Replacing every parent variable by z_i+1
before making records would create more terms and more protected pairs.
Here that entire substitution is paid once, in one addition to the common
convolution factor.

All exponents in these expressions are fixed, nonnegative integers. Each
fixed power and geometric sum is expanded into a finite division-free DAG.
No new intermediate register is an additional quantified unknown.

### Unconditional positivity

Because B-1>M, the unique positive top coefficient gives

`Dcode > 2B^hmax - M sum_(r<hmax) B^r > B^hmax > 0`.

Also `Dcode < M B^(hmax+1)/(B-1)`. Distinct positive weights give
`ell < B^(W+1)/(B-1)`, and b-1 < B-1; hence Mask>0. Thus Tcode,
Jcode, Scode and R are positive for every outer assignment, whether or not
the encoded equations hold. In particular R>=N>=8 and b<=R,N. These are
the unconditional hypotheses required by the later numerical ratio theorem.

### Bounds after the ratio theorem bounds g

If `g<4bB^W`, then g<N0 because 4b<B. Further,
`1+ell<2B^W`, so `1+ell+g<5bB^W`. Consequently

`2(1+ell+g)^2 Dcode < 50M b^2 B^(K+1)/(B-1)`.

Since b>=8192M, this is less than `B^(K+1)/32`. The geometric summand
is less than `2B^(K+1)`. Therefore `0<Jcode<N1` and `0<Scode<N`.
The inequality `(B-2)Targets<B^(hmax+1)` similarly gives `0<Tcode<N`.
These estimates use only the displayed numerical bound on g, not the
carry condition or the existence of a parent zero.

## 3. The carry test and the positive parent

Suppose b is a power of two and `g<4bB^W`. N, N0, N1 and B are powers
of two. If `N=2^r` and `0<=S,T<N`, then exactly

`(N-1)[(S+T+1)N+T+1]=(S+T)N^2+(N-1-S)N+(N-1-T)`.

The three blocks do not overlap. Thus the binary population count is
`popcount(R)=2r+popcount(S+T)-popcount(S)-popcount(T)`.
The last three terms are minus the number of binary carries, counted with
multiplicity. Legendre's factorial formula also gives
`v_2(binomial(2R,R))=popcount(R)`. Therefore

`N^2 | binomial(2R,R)`

is equivalent to no binary carries in Scode+Tcode. Because their low blocks
lie in [0,N0) and their high blocks in [0,N1), this is equivalent to both

`tau_2(g,Mask)=0` and `tau_2(Jcode,(B-2)Targets)=0`.

The first mask has digits B-b at the 31 allowed weights, B-1 elsewhere
through W. Hence it is equivalent to

`g=sum_i z_i B^w_i`, with `0<=z_i<b`.

Put x_i=z_i+1. Then `1+ell+g=1+sum_i x_i B^w_i`, with 1<=x_i<=b.
Every coefficient of C_x(t)D(t) has absolute value less than
`M(1+sum_i x_i)^2 <= M(32b)^2 <= B/8 < B/2`, using b>=8192M.
Its degree is at most K. Consequently, if
`a_r=[t^r]C_xD+B/2`, then `0<a_r<B` and

`Jcode=2 sum_(r=0)^K a_r B^r`.

Both operands in the second carry test are even. Dividing both by two is
a common binary shift, so it preserves the absence of carries. At each
target position, the second operand has digit B/2-1. Its binary support
is exactly all the lower bits of the cell. A digit 0<a_h<B is disjoint
from that mask exactly when a_h=B/2. Thus the target carry test holds if
and only if all extracted coefficients vanish, equivalently
`p_1(x)=...=p_22(x)=0` with all x_i strictly positive.

Conversely, given a positive common zero x, choose an arbitrarily large
power of two b>=b_floor with b>max_i x_i. Set z_i=x_i-1 and encode g as
above. The parent cannot vanish at the all-one vector: its fourth residual
`a-E-sN` there equals -1. Hence g>0. Also
`g <= (b-1)ell < bB^W`, so `32g<Gcap`. Both carry tests hold, and
the central-binomial divisibility follows. This gives exactly the stronger
completeness bound required by Jones's ratio theorem.

## 4. Ratio bridge and single-polynomial finalizer

Use the following registers, exactly as in package 45:

```
U=N^2 w, Y=N^2 s, M0=RY, P=2 M0^2 U,
K1=R+1+h(P-1), A=M0(U+1), B1=2R+1, W1=bw,
C=B1+W1+phi, J=4A-5,
Q=3W1 C-2(W1^2-1),
D1=(A^2-1)C^2+1, E=i J D1 C^2,
F=(A^2-1)E^2+1,
G=A+F(CD1+1-A), H1=B1+jC,
I=(G^2-1)H1^2+1,
a0=(P^2-1)K1^2+1, a1=D1 F I,
u=JF, v=QF+J(H1-C),
m=K1^2 Gcap-4(C-K1Y)^2 Gcap-8gK1^2.
```

The names K1,D1,H1 here avoid confusion with the source degree K, source
polynomial D(t), and coefficient bound H. The executable circuit retains
the package-45 tail register names.

The arithmetic theorems `Jones1982.Nine.ratio_sound` and `ratio_complete`
are the only imported ratio facts. Their numerical hypotheses are R,N>=8,
b<=R,N, b,Gcap>0, h,s,w,i,j>0 and phi>=0, all supplied above. Soundness
says a0,a1 square, u|v and m>0 imply b a power of two, the central-binomial
divisibility and `8g<Gcap`, i.e. `g<4bB^W`. Completeness starts with b a
power of two, that divisibility and `32g<Gcap`, and supplies the ratio
witnesses. Section 3 gives precisely these two directions without circular
dependence on the carry condition.

Put

```
V0=PK1, V1=(AC)(AE)(GH1), Mdiv=Q+H1,
Omega=um,
Theta=u(n+Mdiv)+v-Omega(2Mdiv+V0V1),
F9=(Theta^2-Omega^2(a0+V0^2 a1))^2
   -4 Omega^4 V0^2 a0 a1.
```

The requested single equation is **F9=0**. All auxiliary names in this
formula are polynomial abbreviations in the same nine unknowns.

For completeness, the finalizer proof is short. Unconditionally a0,a1,u
are positive; the norm identities show `0<a0<V0^2`, `0<a1<V1^2`.
Also `0<v/u<Mdiv-1`. If m=0 then Theta/u=n+Mdiv+v/u>0, so F9 is
nonzero. Otherwise the four-factor norm identity gives
`Theta/Omega=r0+V0 r1` for real roots r_t^2=a_t. This rational number
cannot be zero, since then `|r1|=|r0|/V0<1` but r1^2 is a positive
integer. The identity `2(Theta/Omega)r0=(Theta/Omega)^2+a0-V0^2 a1`
makes both roots rational, hence integers. Their strict majorants give
`|r_t|<=V_t-1`. Thus

`Z=2Mdiv+V0V1+r0+V0r1>=2Mdiv+1>0`.

The vanishing factor is `n+Mdiv+v/u=mZ`. Its positive left side forces
m>0; integrality then forces u|v. Conversely, if the two a_t are squares,
u|v and m>0, choose integer roots and set `n=mZ-Mdiv-v/u>=2`; the
corresponding factor vanishes. This proves both directions of the finalizer.

The fixed parent theorem now gives

`exists nine-domain zero of F9` iff `there exists a finite ZFC refutation`.

Negating yields the intended equivalence with Con(ZFC). The displayed
argument is ordinary arithmetic formalizable in ZFC and uses no consistency
assumption. It remains distinct from a newly compiled end-to-end object-
language ZFC or Lean certificate for the complete explicit construction.

To obtain nine positive coordinates replace epsilon,phi,n by positive
coordinates minus one. To obtain nine nonnegative coordinates replace
g,h,s,w,i,j by their coordinates plus one. These are domain bijections;
neither permits silently treating F9 as an equation over unrestricted Z.

## 5. Exact degree and implementation checks

Let `t=deg N=3(hmax+3W+2)`, so t=17,025 here. On the all-variable
diagonal, N has leader 4 and R has leader 16 and degree 3t. In Jcode, the
geometric summand has degree 3(K+1), strictly exceeding the modified
convolution summand's degree 3K. Thus the new common positivity shift
does not alter any leading term in the package-45 tail calculation.

The decisive cancellation is resolved with the exact identity

```
V1^2-a1 = (C^2-1)(AE)^2(GH1)^2
          +D1(E^2-1)(GH1)^2+D1 F(H1^2-1).
```

Writing this right side as DeltaV and
`E0=u(n+Mdiv)+v-2Omega Mdiv`, the exact inner polynomial becomes

```
E0^2-2E0 Omega V0V1+Omega^2 V0^2 DeltaV-Omega^2 a0.
```

Its uniquely largest degree is `576t+6W+140`, with diagonal coefficient
`2^1025`. The final subtracted term has strictly smaller degree than its
square. Therefore

`deg F9=1152t+12W+280=19,615,180`,

and the diagonal leading coefficient is `2^2050`. The same degree envelope
holds for full multivariate total degree, so this nonzero diagonal term
proves exact degree, rather than only an upper bound.

`build_nine.py` exports the primary and cancellation-resolved circuits in
both domains. `verify_nine.py` independently checks all active and cross-
target pair conditions, all 94 sparse records, operation counts, liveness,
data hashes, both domain maps, direct source evaluation, 352 independent
positive-offset target extractions, primary/certificate polynomial replay,
the exact degree certificate modulo three primes, 128 finalizer completeness
fixtures and 980 zero-margin exclusions. The coefficient payloads are hashed
and read as exact integers. These checks audit the finite implementation;
the unbounded semantic argument is the mathematical proof above.

## Reproduction

```
python3 build_nine.py
python3 verify_nine.py
python3 -O verify_nine.py
```

The code uses only the Python standard library and works with assertions
disabled. The copied package-45 builder, circuit helper and proof in
`upstream/` document the retained ratio/finalizer and carry identities.
