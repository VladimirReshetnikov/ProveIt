# A prefix code reduces the explicit universal construction to 1057

The explicit U15,2 construction now costs **1057 = 429M + 628A**, with
**163 positive existential coordinates**, 27 comparisons and three positive
program parameters. Its certificate costs **977 = 402M + 575A** and its
degree is **201682**. Keeping the initial history value supplied gives
**1060 = 430M + 630A**, 164 witnesses, 28 comparisons and degree **7332**.

Both alternatives save 15 operations over their respective 1072/1075
parents, use one additional witness, and lower the degree. The fixed
97-tile U15,2 computation and ordinary positive input contract are unchanged.
This is a complete alternative to, and not an improvement on, the existing
75-operation certificate or 88-operation universal polynomial.

## 1. A fixed injective code

The [explicit-machine parent](neary_woods_explicit_universal_tm.md) gives
the actual transition table, effective per-language initialization and
paid positive arithmetic. Its source and primary-source audit remain the
universality premises here; no new machine simulation is asserted.

Replace the five-bit code for every symbol by the following binary prefix
code. Tape blank `c`, renamed `_` in the source, has code `00`; tape `b`
has code `01`. The 15 ordinary states use the 15 five-bit words starting
with `1` other than `11111`. The four remaining symbols extend `11111`
by two bits. The final fixed assignment is:

| Symbol | Code | Symbol | Code | Symbol | Code |
|---|---|---|---|---|---|
| `_` | 00 | b | 01 | u1 | 10010 |
| u2 | 10001 | u3 | 11110 | u4 | 11101 |
| u5 | 10011 | u6 | 11011 | u7 | 11010 |
| u8 | 11001 | u9 | 10000 | u10 | 11100 |
| u11 | 10100 | u12 | 10110 | u13 | 10101 |
| u14 | 10111 | u15 | 11000 | `[` | 1111101 |
| `]` | 1111110 | `#` | 1111111 | halt | 1111100 |

Call the induced monoid homomorphism `h`. Its codewords are prefix-free:
the tape words start with `0`; the five-bit state words leave only the
`11111` branch; that branch has four distinct length-seven leaves. Greedy
decoding is therefore unique, including at every concatenation boundary.
Consequently

\[
 h(v)=h(w)\quad\Longleftrightarrow\quad v=w.
\]

For a physical word `w`, define

\[
 \ell(w)=|h(w)|,\quad v(w)=\operatorname{val}_2(h(w)),\quad
 c(w)=2^{\ell(w)}+v(w).
\]

Then `c` retains leading zero bits and satisfies
`c(uv)=2^ell(v)c(u)+v(v)`. Each physical tile `(u,v)` becomes the literal
affine map

\[
 (U,V)\longmapsto
 (2^{\ell(u)}U+v(u),\;2^{\ell(v)}V+v(v)).
\]

These are fixed positive slopes and nonnegative offsets, exactly the domain
of the complete affine-pair history compiler. It never requires all physical
symbols to have the same bit length.

Although the bit pattern for `#` can occur inside a longer concatenation,
this creates no new derivations. The compiled objects are whole tile images.
An equality of their complete concatenations uniquely decodes to equality
of the original physical words. In particular,

\[
 h(\sigma(w)\#t)=h(i\#\tau(w))
 \iff \sigma(w)\#t=i\#\tau(w).
\]

Thus the parent's fresh-delimiter proof and state-copy deletion apply on
the same valid physical initializations. This is an equivalence of word
existence, not an identity on old and new arithmetic witness tuples.

## 2. The ordinary-input block is 64 bits

The unchanged physical blocks are

\[
 A_i=(cb)^{8i-5}bb,\qquad B_0=A_2A_1,\quad B_1=A_1A_2.
\]

Each bit block still contains 32 tape symbols. Both tape codewords have
length two, so both images now have exactly **64 bits**, instead of 160.
Let `C0=v(B0)` and `C1=v(B1)`. Their first differing physical symbols are
`c` and `b`, respectively, so `0<C0<C1<2^64`.

Use the complete generic-width recoder with `k=64`, obtaining

\[
 q=2^n,\quad n\ge2,\quad 0<x<q,\quad Q=q^{64},\quad
 z=\sum_{j<n}\operatorname{bit}_j(x)2^{64j}.
\]

The five paid block gates and repunit comparison remain:

\[
 (2^{64}-1)R+1=Q,\qquad D=C_0R+(C_1-C_0)z.
\]

Thus `D` is the binary value of the concatenated bit-block images for the
length-`n` padded input. All padding still means leading **physical zero
pairs**, which the represented semidecider ignores. No leading tape cells
are discarded by the shorter code.

For each r.e. set, keep the parent's physical prefix and suffix but choose
the three program parameters using the new code:

\[
 p=c(\text{prefix}),\quad a=2^{\ell(\text{suffix})},\quad
 b=v(\text{suffix}).
\]

The suffix includes the nonzero code of `#`, so all parameters are positive.
The same four gates compute `Vi=a(pQ+D)+b`. The terminal word is still
`# [ halt ]`; its new 28-bit image supplies two fixed terminal constants,
both explicitly rebuilt in the source. The code map and all fixed
multipliers are compiler data; every runtime product with them is charged.

On arbitrary positive supplied coordinates, `R,z,p,a,b>0` and `C1-C0>0`
make `D` and computed `Vi` positive before any typing equations. This is
the positivity condition needed by the native projections. Complete old
word witnesses give complete new witnesses by the full recoder and history
converses, using fresh native coordinates. Conversely, decoded new witnesses
give exactly the same physical word and hence the same halting decision.

It follows that the fixed new polynomial satisfies, for every r.e. `S`,

\[
 x\in S\iff\exists y_1,\ldots,y_{163}>0:
 F(x,p_S,a_S,b_S,y_1,\ldots,y_{163})=0.
\]

Arbitrary positive program triples need not be valid machine encodings.
Universality uses the explicitly constructed valid slice for each set.

Within the restricted class that keeps these physical 32-symbol blocks and
assigns equal-length binary prefix codewords to `c,b`, width 64 is minimal.
If that common length were one, the two tape words would exhaust both root
branches, leaving no codeword for a state or delimiter. This is not a global
lower bound on recoding, unequal-length codes or arithmetic complexity.

## 3. Paid history and exact counts

Ordinary moves have coded source and target length 9. A tape-boundary source
has length 14 and its target length 16. The halt adapter has lengths 7/9;
cleanup has lengths 9/7. Copy lengths are 2 or 7. Therefore the two slope
length sets are

\[
 \{2,7,9,14\},\qquad\{2,7,9,16\}.
\]

The [paid history planner](gpcp_slope_class_compiler.md) chooses baseline
`512` in both coordinates, leaving three exceptions on each side. With
`s=97`, this gives `g=6` selected products and scale exponent `N=107`.
The chosen literal history costs **823 = 316M + 507A**. The final code map
was selected by a bounded search over length-preserving codeword
permutations. It is not claimed optimal. The source stores the complete
literal assignment and reruns the actual baseline/fallback planner; it
does not depend on the search script or a cached cost assertion.

The recoder needs six binary-chain multiplications for `q^64`, two fewer
than for `q^160`. Its raw 134 gates, the eleven paid framing/block gates
and nine native-unit product gates add `86M+68A` to the history. Hence

\[
 C=823+154=977=402M+575A.
\]

The unchanged unit argument combines nine sign-safe norms with one checksum
and keeps the second checksum separately constrained. The repunit and all
other outer residuals stay paid. Finalizing the 27 comparisons as
`U(1+sum outer_residual^2)-1` adds `27M+53A`, giving **1057** operations.
The witness count is `s+g+60=163`. Supplying `Vi` adds one witness and one
comparison, giving **1060** operations at the same certificate cost.

## 4. Degree and comparison schedules

The inherited exact-degree audit checks every gate prerequisite of the
three main-norm cancellation identities, propagates actual homogeneous
degrees through this new DAG, and proves attainment by a nonzero unit
leading coefficient times a positive outer sum of leading squares.
With `k=64`, set `v=k+2=66`, `nu=k+3=67` for computed `Vi` or `nu=2` for
supplied `Vi`, and `d_H=107nu`. Then

\[
 \deg F=14+19v+20d_H-6\nu+84+8\max(d_H,v).
\]

The computed variant has unit degree 144310 and maximum outer residual
degree 28686, hence degree **201682**. Supplying `Vi` gives degrees 5600
and 866, hence **7332**. Program-prefix and suffix-scale parameters each
contribute their paid multiplication to the computed input degree; treating
them as fixed constants in this universal four-free-variable polynomial
would give an incorrect degree.

The receipt retains other complete schedules for comparison:

| Code | k | History H | g | Polynomial, computed Vi | Degree | Supplied Vi polynomial / degree |
|---|---:|---:|---:|---:|---:|---:|
| Tuned lengths 2/5/7 | 64 | 823 | 6 | **1057** | 201682 | **1060 / 7332** |
| Ordered lengths 2/5/7 | 64 | 831 | 6 | 1065 | 201682 | 1068 / 7332 |
| Tape length 2, all other lengths 6 | 64 | 856 | 8 | 1090 | 205434 | 1093 / 7444 |
| c=0, b=10, other lengths 7 | 50 | 1011 | 15 | 1246 | 172912 | 1249 / 7570 |
| c=10, b=0, other lengths 7 | 46 | 1016 | 16 | 1252 | 161240 | 1255 / 7550 |

The last row reverses the two physical bit blocks so that the fixed
coefficient difference stays positive. Its represented semidecider uses
that reversed bit-pair convention. Shorter blocks alone do not guarantee
cheaper histories: unequal tape lengths create more slope classes.

## 5. Reproduction and audit boundary

```sh
/tmp/diophantine-research-venv/bin/python neary_woods_prefix_universal.py
```

The receipt includes one complete tuned source and finalizer, its full code
map and 97 actual affine tile maps, ten compact ledgers/degrees, and all
paid history candidate costs. Tests check prefix decoding and sentinel
concatenation, independently accumulated complete tile words, positive
frames with variable padding, and full signed polynomial identities through
the native-unit projections. They do not materialize enormous complete
Pell zeros, and finite fixtures are not used as a universality proof.

The parent's primary-source table audit, exact initial-head convention,
nonhalting rejection convention and permanent boundary-marker argument
remain in force. This construction uses U15,2 throughout and has no
dependency on the malformed singleton-`A` U9,3 boundary example.

Independent root proof/source review and native-controller full
proof/source/fresh-default review passed without findings. The latter also
checked 480 independent tile-word append/injection cases, 320 exact padded
frames, and 64 direct scalar-norm/full-polynomial evaluations, including
32 signed assignments. Root independently checked 24 signed history
residual/interface identities for the tuned code assignment. These checks
supplement the proofs and do not materialize full native Pell witnesses.
