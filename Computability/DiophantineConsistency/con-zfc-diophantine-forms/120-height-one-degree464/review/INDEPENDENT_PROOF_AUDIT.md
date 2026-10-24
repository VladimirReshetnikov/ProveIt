# Independent audit: eleven integers with a degree-464 candidate

Audit scope: ordinary mathematical composition of the incoming selective
coprime fusion and powered-saturation lemmas, at ProveIt commit
`45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6`. This audit does not certify an
end-to-end proof-assistant theorem or the inherited native compiler. Its
source files and hashes are recorded in `source_pins.json`.

## Exact proposed change

Keep all eleven coordinates, the complete source34 six-coefficient tuple,
the centered budget, the three-root norm, and all other abbreviations of
`ZFC_Diophantine_Coprime_Projection/integer/PROOF.md` unchanged. Replace

```
I = 2*s*r*c^2,     S = I*H^5
```

by

```
I = 2*r*c^2,       S = s*r*H.
```

Use the auxiliary center `Q*V`. Replace the guard by
`Dg=1+(3*Budget-4)*Dt*s^2` and retain `P=Dt*Dg`. The three
norm radicands, in strong/auxiliary/fused order, are `4*S^2*Df`,
`S^2*Da`, and `16*S^2*P`.

This changes the polynomial. The assertion is equivalence of existence of
integer zeros, using fresh auxiliary witnesses, rather than equality of
polynomials or preservation of every old auxiliary assignment.

The guard factor and root-weight changes are justified explicitly below.
The selected norm uses weights 2, 1, 4, which retain distinct 2-adic
valuations while permitting the shorter center `Q*V`.

## 1. Nonzero and sign bootstrap

The unconditional source facts remain valid: `q` is even, `q=2 (mod 3)`,
`|q|>=beta-1`, `|X|>=4|q|`, `|Y|>=|q|^3`, `H!=0`, and `Delta>1`.
The integer `Dt=1+ell*(ell+1)*k^2` is positive and odd. Also `Df>=1`.

At any zero, `S=0` would make the norm exactly `Ac^8`. Here
`Ac=H^5*pi(T+K/H)` with `pi(u)=(u^2+3)*(u^3-19)`. This is nonzero:
the quadratic has no real root, and the cubic has no rational root.
Consequently `S!=0`, so `s!=0` and `r!=0`. This step does **not** imply
`c!=0`; the next steps must handle that case.

If `c=0`, then `I=0`, `Q=0`, `delta=-1`, `Cy=-1`, and `Da=1`.
If `c!=0`, then `|I|>=2*c^2`; hence `Df>|c|+1`. For the integer
`b0=c-R+4*I*T`, either `b0=0` and `|V|=|c|>=1`, or
`|V|>=Df-|c|>1`. Thus `Q>1`, `Cy>0`, and `Da>0`.
In either case `Da` is positive.

A vanishing conjugate factor cannot have `Dg<0`: the `P=Dt*Dg` term
would be its sole nonzero imaginary summand. Section 7 shows that `Budget` is a multiple of 4, hence `Dg=1 (mod 4)`
and `Dg` is positive. If `Budget<=1`, then `Budget<=0`, so
`3*Budget-4<=-4` and, using `s!=0` and `Dt>=1`, `Dg<=-3`, a
contradiction. Thus `Budget>=2`.

This proves `k!=0`, `Derr<q^2` and `|c/k-Y|<1/2`, exactly as in the
centered source. Since the integer `Y` is nonzero, `c=0` is now excluded.
Consequently `I!=0`, `Q>1`, and the auxiliary descent can be used. The
disk inequality also recovers the common nonzero signs of `q,F,C,q-F-C`
and `sign(c)=sign(kY)` without yet assuming `eta>0`.

## 2. Root extraction and the centered rank interface

The new `I` is still even. Thus `Df=Da=1 (mod 4)`; `Dt` and `Dg`,
and hence `P`, are odd. In the rational signed sum

```
2*sqrt(Df) + sqrt(Da) + 4*sqrt(P),
```

each nontrivial squareclass has a unique summand of least 2-adic order.
It cannot cancel. Linear independence of distinct squarefree radicals
therefore makes all three roots integral. Since
`gcd(Dt,Dg)=gcd(Dt,1+(3*Budget-4)*Dt*s^2)=1`, their product being a
positive square makes each factor a square. Adjacent-coefficient Pell
descent then makes the auxiliary root `y=sqrt(Da)/delta` integral.
The norm factor now proves `S|Ac`.

All hypotheses needed before the main projection survive the change:
`c^2|I`, `|I|>=|c|`, the strong and auxiliary Pell equations, both
auxiliary congruences `V=-c (mod f)` and `V=-R (mod c)`, the centered
strip, common signs, and the first Pell equation. The odd-multiplier
assumption is not used. In particular, the explicit Lucas-composition
proof in centered11 section 5.2 establishes the stronger rank divisibility
from `c^2|I` even though `I/c^2` is even.

Absolute folding first recovers `|c|=Y_{|a+2|}(p)`. The signed rank
argument then gives `p=R=2t+1`, `t>=24`, and

```
|Y| > (|X|-3)^t/2 - 1,
|H| > |X|*(|X|-3)^t.
```

The new proof must cite only this pre-projection portion at this stage;
calling the entire centered source theorem here would be circular.

## 3. Weakened divisibility still forces exact projection

Let `Kquad=X*(X+2*a*c)-1` and let `K=X*(3*c-2*X)+2`, the short
carrier polynomial of the coprime source. The exact identity is

```
K = H*X*c - 2*Kquad.
```

Because `H|S` and `Ac=(H*T+K)^5 (mod H)`, `S|Ac` gives `H|K^5`.
As `H` is odd, this implies `H|Kquad^5`. Set `sigma=sign(c)` and

```
Pi=(sigma*X-2^R)*(2^R*sigma*X+1).
```

The signed Pell projection identity is
`2^R*Kquad=Pi (mod H)`. Raising the exact congruence to the fifth
power proves `H|Pi^5`. No nonunit is cancelled modulo `H`.

Write `x=|X|`. The actual unchanged coefficient beta gives `x>=2^64`.
The inequalities

```
|Pi|^5 < 2^(20*t+20)*x^10,
|H| > x^(t+1)/2^t
```

imply `|Pi|^5<|H|`, because
`64*(t-9)-(21*t+20)=43*t-596>=436` for `t>=24`.
Thus `Pi=0`. Its second factor is odd and nonzero, so
`sigma*X=2^R`. The remainder of the centered-source orientation,
half-binomial recovery, and fresh odd-kernel reconstruction applies.

This confirms that the powered-saturation bound from the twelve-variable
determinant-guard source transfers to the centered-budget source: its
proof uses exactly the common pre-projection rank and ratio bounds, not
the determinant guard itself.

## 4. Completeness with a fixed strong pair

The same canonical source witness gives `A=a+2>1` even,
`R=3 (mod 4)`, `c=Y_A(R)=R (mod 4)`, and a positive centered budget.
These congruences are explicitly supplied by the centered source and must
not be dropped from the interpolation statement.

Put `N=(3*Budget-4)*Dt`. Since `Dt=1 (mod 3)`, this is a positive
integer equal to 2 modulo 3 and hence nonsquare. A positive Pell unit
supplies positive `s,g` with `g^2=1+N*s^2`.

Choose one positive strong Pell pair with `4*s*c^2|I`, then set
`r=I/(2*c^2)`. This is positive and is divisible by `2*s`. Every prime
factor of `M=s*r` therefore divides `I`. Keep `I,f,r` fixed thereafter.

The supported-modulus interpolation theorem in Round14 radicals section 5
applies to this same centered-source auxiliary chart. It supplies every
residue class of `T` modulo `M`, with the fixed strong pair and an
integer auxiliary root. The proof uses only the canonical even base,
`R=3 (mod 4)`, `c=R (mod 4)`, `4*s*c^2|I`, and the fixed Pell pair;
it is independent of the determinant versus centered guard.

The canonical main projection gives `H|K`; put `kappa=K/H`. Intersectivity
supplies a residue satisfying `pi(T+kappa)=0 (mod M)`. Therefore

```
Ac/S = H^4*pi(T+kappa)/(s*r)
```

is integral. Finally choose

```
n = Ac/S + 2*f + delta*y + 4*tau*g - Q*V.
```

This makes a conjugate norm factor zero. The order is: native outer
witness, guard unit, one strong pair, the intersective residue, auxiliary
`T,y`, then `n`. No strong-pair parameter changes after the residue is
specified. The old auxiliary assignments are not reused pointwise.

## 5. Supported-modulus interpolation review

The original fixed-pair theorem gives a starting index `nu0=3 (mod 4)`
and an auxiliary value `T0`. For `I=Y_A(m0),f=X_A(m0)`, the exact
period modulo `f^2` is `lambda=4*m0*f`; replacing it by `4*m0` would be
invalid. Set `d=lcm(lambda,4*I)`. The standard rank valuation facts give
`v_p(d)=v_p(4*I)` for every `p|I`.

For `nu(h)=nu0+d*h`, the formula

```
T(h)=[X_{Delta*I}(nu(h))/(Delta*I)+c-f^2*(c-R)]/(4*I*f^2)
```

is integral: the period handles divisibility by `f^2`, while the
odd-index quotient identity handles `4*I`, and these are coprime.
Pell addition and lifting give
`v_p(T(h1)-T(h2))=v_p(h1-h2)` for every `p|I`.

For odd `p|rho`, the term involving `Y_rho(difference)/rho` has valuation
`v_p(difference)`; the first-coordinate difference has strictly greater
valuation. At `p=2`, the latter valuation is
`2*(v_2(rho)+v_2(difference))-1`, still strictly greater because the
index difference is divisible by 4. Thus the argument includes the
2-adic case without treating 2 as an odd prime.

This isometry induces a bijection modulo every supported prime power.
Applying CRT to the corresponding residue classes of `h` gives a single
nonnegative `h` attaining the requested `T` modulo `M`. This proves the
full supported-modulus conclusion, not merely a bounded congruence.

## 6. Degree calculation to bind to the literal artifact

With the modified definitions, the degree ledger is

```
I:3, S:8, Df:18, Q:30, V:23, Da:106,
Dt:34, Dg:60, P:94, Ac:35.
u=4*S^2*Df:34, b=S^2*Da:122, e=16*S^2*P:110.
C0=S*Q*V:61, B=S*n-Ac:35.
```

The exact cancellation
`b-C0^2=-S^2*(Q*(V^2+1)-1)` gives
`omega=(C0+B)^2-b` degree at most 96. In

```
[(omega-u-e)^2-4*(u*e+b*(u+e))]^2 - 64*u*b*e*(C0+B)^2
```

the inner bracket has a unique highest term `-4*b_top*e_top`, degree
232. The last product has degree `34+122+110+122 = 388`, strictly below
464. Hence the leading form is
`16*b_top^2*e_top^2`, degree 464. Each factor has a nonzero leading
form over the authentic coefficient tuple. With
`q0=6*beta*j`, `W0=12*w`, `Y0=2*v*q0^3`, `a0=q0*W0*Y0`,
and `F0=W0*C-q0*z`, independently expanding only these leading forms
gives

```
b_top = 2^12*s^2*r^10*c^16*a0^14*q0^6*F0^2,
e_top = -3*2^10*s^4*r^2*h^6*a0^12*q0^2*Y0^6,
P_top = 9*2^48*s^12*r^24*c^32*h^12*a0^52*q0^16*Y0^12*F0^4.
```

In particular, the coefficient of
`j^260*w^56*v^64*C^4*s^12*r^24*c^32*h^12` is exactly
`2^484*3^318*beta^260`, which is nonzero for the authentic positive beta.
The displayed exponents sum to 464. This is a universal polynomial
degree calculation, not a degree inferred from a numerical sample.

The actual generated selected DAG has 122 live binary operations
(77 multiplications, 24 additions, 21 subtractions), with all eleven
variables and all six coefficient leaves live. The direct companion has
121 operations. `Q*V` is already used in `Cy=(Q*V)*V-1`, so the center
adds only one new live addition.

The direct uncentered norm has degree 488, coming from `b_top^4`.
Keeping the conservative `I=2*s*r*c^2` instead gives centered degree
480 and direct degree 520, with completeness requiring only the original
full-residue theorem because `s*r|I`.

## Conclusion and boundary

No mathematical gap was found in this composition, subject to the
explicit retained unbounded native/compiler/refutation theorems. This
audit is an independent ordinary proof review. Literal circuit counts,
coefficient binding, and exact degree must be checked against the final
generated artifacts separately. Finite diagnostics cannot establish the
unbounded consistency equivalence or global minimality.

## 7. Removing the redundant guard factor 4

The source's two cone constants are even and `q` is even. Therefore both
differences `cone_A*F-q` and `cone_B*C-q` are even, `Derr` is a multiple
of 4, and `q^2` is a multiple of 4. The complete polynomial `Budget`
takes values in `4*Z`. Consequently `D=3*Budget-4` is also a multiple
of 4.

For the modified definition `Dg=1+D*Dt*s^2`, `Dg=1 (mod 4)` holds
without the old external multiplier 4. The same sole-imaginary argument
first makes `Dg` positive. If `Budget<=1`, its divisibility by 4 gives
`Budget<=0`, so `D<=-4` and `Dg<=-3`, using `s!=0,Dt>=1`. Thus the
required positive budget is recovered exactly as before. Fixed 2-adic
radical separation and `gcd(Dt,Dg)=1` are unchanged.

For completeness, `N=D*Dt` is again positive and 2 modulo 3. Ordinary
Pell existence directly supplies positive `g,s` with `g^2-N*s^2=1`;
squaring this unit is unnecessary. After choosing this `s`, select the
fixed strong pair with `4*s*c^2|I` as in section 4. Supported-modulus
interpolation, the carrier, and the final choice of `n` are unchanged.

The term degrees are identical. Relative to a graph with the same root
weights and the old external guard factor 4, this change divides the
leading coefficient of the complete degree-464 polynomial by 16.
The separate permutation of strong/auxiliary weights is also reflected
in the literal coefficient certificate. These optimizations change the
polynomial but preserve zero existence by the reviewed ordinary argument.
