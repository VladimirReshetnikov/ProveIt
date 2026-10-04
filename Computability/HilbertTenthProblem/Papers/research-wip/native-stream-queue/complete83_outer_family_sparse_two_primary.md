# Sparse compiler coefficients give the two-primary condition from n=5

For the actual original powers-of-five modified75 compiler, the constructed outer family passes the two-primary cubed-scale condition for every allowed n>=5. The new ingredient is the binary sparsity of its literal clause coefficients. No odd-prime condition, complete positive zero, rejected ordinary input or universal83 assertion follows. The first family member n=1 remains outside this theorem.

## 1. Exact clause and layout counts

Use a for tile-alphabet size, k>=2 for number of allowed windows, and M for the original layout M0. These are distinct from the outer source coefficient K=DC+B*DR. Write the clause radix as A=2^w, w>=2, and t>=0 for the number of appended zero-expression parity clauses. The actual clause recipe in complete78 Section1 has one occupancy clause,9a tile-copy clauses,4 anchor clauses and t zero clauses. Its mask therefore has

`pc(mu)=w-1+9a+4+t=w+9a+3+t`.

The retained complete77/76 recipe uses N=|E|=2pc(mu)+12a+3 native positions and at least one dummy. Selector exponents are0,...,k-1; tile copies run through exponent k+12a-1. The N-(k+9a+4) dummies are consecutive immediately above them, and the four anchors are placed separately. Thus

```
E0=N+3a-5,
M=E0+3a+1=N+6a-4=2w+36a+5+2t,
M>=k+15a.
```

The top parity mask is at clause position9a+4+t, so mu>=2^(w(9a+4+t)). Since the compiler chooses V=2^b>2mu, it has b>w(9a+4+t). In particular b>26 and, being a power of5, b>=125. Also b>2(9a+4+t) and b>2w, so

`M<3b`.

These bounds concern the unmodified center clauses; allowing the extra ignored dummy bit does not change any c_e or mu.

Each selector occurs once in occupancy, once in each of its nine tile-copy clauses, and once in each of four anchor clauses. Its coefficient c_e therefore has exactly14 set bits, all at distinct clause positions. Every tile-copy or anchor coefficient has one set bit, and dummy coefficients vanish. Hence

`sum_e pc(c_e)=14k+9a+4`.

The four explicit DC monomials, two clause bands, optional single high monomial, and B*DR give the safe binary-population estimate

```
pc(K)<=2(14k+9a+4)+6<=30M.                       (1)
```

This uses subadditivity pc(U+V)<=pc(U)+pc(V), so it does not require separate support for every summand. The unique lowest monomial of K is V^(3a), with coefficient1: all four-anchor shifts, clause bands, optional high term and B*DR have strictly higher exponent. Therefore

`v2(K)=3ab`.                                      (2)

## 2. Count the deficits, rather than their bit lengths

Retain B=2^d, d=bL, L>213M+4a+4, and the unchanged outer family: z=1 mod4,1<=z<=4d,F=Kz,Q=B^n,D=dn. Put P=pc(F) and v=v2(F). Since z is odd, (2) gives v=3ab. Binary product subadditivity yields

```
P<=pc(K)pc(z)<=30M(log2(d)+3),
3v=9ab<=3bM/5.                                  (3)
```

The latter uses M>=15a. The established high-digit proof applies already for n>=5 because Q>Astar. Its three complement digits are Q-a_i. Their total population is exactly3D-Loss, where

`Loss=sum_i pc(a_i-1)`.

For the plus shape, the three deficit-minus-one quantities are

```
6F+4z+2-epsilon, 6F-4, 2F-6,    -1<=epsilon<=9.
```

For the minus shape they are

```
6F+4z+2-epsilon, 8F-25, 32,     -1<=epsilon<=8.
```

If the first small correction delta=4z+2-epsilon is nonnegative, binary subadditivity bounds its population by2P+pc(delta), with pc(delta)<log2(d)+6 whenever delta>0 (and zero when delta=0). If delta is negative, its magnitude is at most3. For a positive integer T with v2(T)=h and0<c<2^h,

`pc(T-c)=pc(T)-1+h-pc(c-1)`.                      (4)

Indeed write T=2^h U with U odd; T-c=2^h(U-1)+(2^h-c), whose two bit ranges are disjoint. Applying (4) to6F gives the bound2P+v. Thus in both cases the first deficit population is at most2P+v+log2(d)+6.

The other populations follow from (4), since v=3ab>=375:

```
pc(6F-4)=pc(6F)+v-2<=2P+v-2,
pc(2F-6)=P+v-2,
pc(8F-25)=P+v,
pc(32)=1.
```

Both shapes therefore satisfy the common conservative estimate

```
Loss <= 5P+3v+log2(d)+6
     <= 151M log2(d)+456M+3bM/5.                  (5)
```

For the minus shape its sharper3P+2v+log2(d)+7 bound is below the common bound because2P+v>=1. In the second inequality of(5), substitute(3), then use M>=1 to absorb the final logarithm and constant.

## 3. The loss is less than half a cell length

For all real L>=213M the function

`[151M log2(bL)+456M+3bM/5]/(bL)`

is decreasing: its derivative has the sign of151M/ln2 minus the numerator, which is negative in this range. Since M<3b,

```
Loss/d < [151 log2(639b²)+456+3b/5]/(213b).
```

For every integer b>=125, log2(639b²)<b/2. An exact base inequality is (639*125²)²<2^125; the ratio2^(b/2)/b² increases because2*125^4>126^4 and the corresponding ratio only improves for larger b. Consequently

```
Loss/d < [151b/2+456+3b/5]/(213b) < 1/2,         (6)
```

where the last inequality holds already at b=125 and strengthens thereafter. These are all-size estimates; no enumeration of compiler constants is needed.

The actual fixed-mask density already proved in the uniform-cutoff note gives pc(MC)>4d/5. The n-3 low MC blocks are disjoint from the three high complement blocks in either shape, including the four-bit shift for16R. Since n>=5 and R is odd,

```
pc(r)>=3D-Loss+(n-3)pc(MC)-1
      >3D-d/2+8d/5-1
       =3D+11d/10-1 >3D+1.                      (7)
```

The last inequality uses d>=3125. The accepted unique-central-term argument gives the exact full valuation v2(M_r(X))=pc(r). As v2(q) is D-1 or D, (7) proves the required2-primary scale condition. The new estimate changes no source operation or compiler numeral.

## 4. Proof dependencies and boundary

The exact clause census uses complete78 Sections1–2, the one-marker native-position count from complete77 Section1, and complete76 Section1 plus modified75 Section1. The sparse coefficient definitions are retained literally; this proof does not apply to arbitrary synthetic positive K with the same magnitude. The high-digit identities, their corrected constant terms, the conservative epsilon ranges and disjoint bit positions are inherited from the reviewed eventual two-primary packet. The density result is inherited from the reviewed uniform-cutoff packet; its simple support proof is also given above through its stated inequality.

Odd-prime completion remains independent. This theorem does not choose an arbitrary input, does not construct huge Pell values, and does not prove a noncanonical zero or language failure. n=1 is not addressed, and no optimal cutoff claim is made.

## 5. Fresh evidence and freeze scope

The new helper authenticates seven source files as inert bytes. It independently creates four explicitly synthetic selector/clause assignments, follows the displayed native coefficient formulas, and checks the exact clause census, minimum binary valuation, complement population, and sparse K bound. These are relaxed symbolic layouts, not universal machines or compiler-language examples. Across both optional-high-term choices, the constructed K has at most10,321,126 bits. The checker tests252 signed-deficit cases spanning every conservative carry value and three z sizes, and4,052 exact instances of the subtraction identity. Exact integer comparisons check the logarithmic base/ratio and final rational margin. No R, X, Y, complete source zero or Pell tuple is materialized.

Fresh writer, normal and optimized-Python exact receipt checks passed before freezing. Only this new helper ran; no supplied, committed, archived, frozen or copied predecessor program was executed or imported. The finite checks corroborate the quantified proof and do not replace it. The inherited circuit count, degree, compiler semantics and Pell completion are not newly certified. A separate independent review challenges the source census and every new inequality.
