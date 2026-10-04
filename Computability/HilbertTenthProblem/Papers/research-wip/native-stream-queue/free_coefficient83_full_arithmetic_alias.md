# A full arithmetic wrong-index zero at diagnostic numeral ports

The [83-operation candidate](complete83_free_coefficient_scout.md) has a
**full positive integer zero** with all seven intended factor values and a
main Pell index different from its actual computed packing index. The fixed
numerals in this construction satisfy the displayed power, repunit, mask,
population and size conditions, but **are not a valid fixed-program recipe**.
Thus this is an obstruction to deriving index recovery from those arithmetic
conditions alone. It is not a false accepted ordinary input for a universal
compiler, and it neither proves nor refutes the candidate's universality.

The enormous positive witnesses are defined constructively by Pell sequences
and CRT. They are not materialized. The [fresh helper](free_coefficient83_full_arithmetic_alias.py)
and [receipt](free_coefficient83_full_arithmetic_alias.json) check all finite
outer data, the exact modular Pell/CRT conditions, and 16 complete rational
evaluations of the actual 83-row graph. The latter evaluations are off-zero
algebra checks, distinct from the proof-defined positive zero.

## 1. Exact finite outer data and its limitation

Use the following fixed numeral data and supplied ordinary input:

| Quantity | Value |
|---|---:|
| d, b, B | 9, 5, 512 |
| N, q=B^N, J=(q-1)/(B-1) | 3, 134217728, 262657 |
| MC, native MF0, paid MF=MF0+B-1 | 374, 292, 803 |
| Kconstant | 135578 |
| x | 1 |
| F, Z | 64816286, 17584025 |
| alpha | 25844766 |
| u=2dx+b, W=2^u, C=Z+W | 23, 8388608, 25972633 |

The six actual fixed ports are `Bm1=511`, `MC=374`, `MF=803`,
`Kconstant=135578`, `twice_cell_bits=18`, and `inner_bits=5`.
Every one is positive. Put

```
t=9159759548913079,
p=t(t+2)=83901194993904350801009395086399,
n=t(t+1)=83901194993904341641249846173320,
R=2n-1=167802389987808683282499692346639.
```

These are positive integers, t is odd, p and R are 3 modulo 4, and
`R-p=t²-1>0`. The exact packing computation is

```
G=q²-qF-Z=9314903847579751,
R=G(q²-1)+(MC+q*MF)J.
```

It satisfies `F+Z<q` and `(2q-1)(q²-1)<R<q⁴-q³`. The masks have
`0<MC,MF0<B-1`, `MC=2 mod4`, `MF0=4 mod8`, and
`popcount(MC)+popcount(MF0)=6+3=d`. Also `0<Kconstant<B²`.
These are necessary arithmetic conditions, not a sufficient compiler recipe.

In particular, the actual recipe requires an integral radix layout with
`B=(2^b)^L`; here b=5 does not divide d=9. The required powers-of-five width
condition also fails. No universal machine, admissible compiled window layout,
or accepted language is assigned to these numeral ports. The diagnostic is
stronger than an untyped native subsystem example because it satisfies the
literal full circuit, including its input and transport factors; it remains
outside the theorem's valid fixed-program slices.

## 2. First and main factors, with the actual packed target

Use the family proved in [the scaled obstruction](first_index_scaled_obstruction.md):

```
X=2^p, Y=2^(t+1), E=XY,
a=Y(X+1), A=a+2, Delta=A²-1, H=4a+3,
P=2XY²+1,
(D,c)=(chi_A(p),psi_A(p)),
(tau,k)=(chi_P(n),2psi_P(n)).
```

That proof establishes both positive Pell norms, the strict inequalities
`kY<c<k(Y+1)`, and the positive integral main quotient

```
gamma=(D-a*c-X)/H.
```

Set `eta=c-kY`, `zeta=k(Y+1)-c`. Both are positive integers and
`eta+zeta=k`. Since p exceeds 27 and t+1 exceeds 81, the source scales hold
with positive integer witnesses `w=2^(p-27)` and `s=2^(t+1-81)`:
`X=wq` and `Y=sq³`.

As P is 1 modulo E, its Pell recurrence gives `psi_P(n)=n mod E`.
Consequently

```
h=(k-2n)/E=(k-R-1)/E
```

is an integer. It is positive since P>1 and n>1 imply `psi_P(n)>n`.
The actual index factor is therefore `k-hE-R=1`, with R now the literal
packing value from Section 1, not an abstract cut. The main Pell index is p,
and p differs from R.

## 3. Restoring the full input factor and the shared positive rho

Set e=u=23 and define

```
kappa=psi_A(e), mu=chi_A(e),
delta=(kappa-u)/Delta,
rho=(mu-a*kappa-W)/H,
sigma=gamma-rho.
```

All three supplied coordinates delta, rho and sigma are positive integers.
For odd e, the Pell binomial expansion gives `psi_A(e)=e mod Delta`, since
`A²=1 mod Delta`. Also `psi_A(e)>e` for A>1 and e>1. Hence delta is a positive
integer and the source's index producer is exactly `u+delta*Delta=kappa`.

For integrality of rho and its comparison with gamma, write

```
g_j=chi_A(j)-a*psi_A(j).
```

Then `g_0=1`, `g_1=2`, and `g_(j+1)=2A*g_j-g_(j-1)`. The sequence `2^j`
satisfies the same recurrence modulo `H=4A-5`, so `g_j=2^j mod H`.
This proves both quotient integrality statements, with `X=2^p` and `W=2^e`.

The positive g sequence is strictly increasing and satisfies
`g_(j+1)>(2A-1)g_j` for j>=1. Here `A>X=2^p>2^e=W`, and e>=3.
The explicit value `g_3=8A²-2A-2` exceeds `H+A`, so `g_e-W>H` and rho>0.
Since p>e, monotonicity and the same growth bound give

```
g_p-g_e >= g_(e+1)-g_e > (2A-2)g_e > X.
```

Thus `gamma-rho=(g_p-g_e-X+W)/H>0`. The shared main-root split
`rho+sigma=gamma` is restored with both coordinates positive. This step is
essential: keeping rho=1 from the earlier native fixture would not furnish
this input equation.

The finite alpha in Section 1 obeys

```
C=q-F-Z-alpha-2dx=Z+W,
W=C-Z.
```

Therefore the actual input root is `W+a*kappa+rho*H=mu`, and its norm is
`mu²-Delta*kappa²=1`. These are the full source expressions, with the ordinary
input x=1 unchanged.

## 4. Positive integral transport quotient

The exact finite modular calculation gives

```
w=2^(p-27)=4096 mod(q-1),
(Kconstant+4096)C+q-F-1=0 mod(q-1).
```

Set

```
transport_quotient=((Kconstant+w)C+q-F-1)/(q-1).
```

This is an integer by the congruence, and it is positive because C>0,
Kconstant+w>0 and q-F-1>=0. Its literal transport factor is exactly 1.
No supplied transport coordinate has been omitted or permitted to be rational.

## 5. Positive auxiliary extension and complete zero

Set `f=D` and `S=Delta*c`, where S is the candidate's supplied
`aux_coefficient_root`. Then `Delta*f²-S²=Delta` by the main norm.
The main c is odd since A is even and p is odd. Independently computed modular
Pell powering gives

```
c mod p=36618251610398372242942694064198,
gcd(c,p)=3,  3 divides R-p.
```

Thus the two conditions

```
v=R mod c,  v=p mod 4p
```

are compatible. The receipt records a finite exact coefficient j such that
`v=R+c*j>0`, found by solving the congruence with c modulo 4p. It never
constructs c itself. In particular v is 3 modulo 4. Define

```
V=chi_S(v)/S, y_aux=psi_S(v),
auxiliary_quotient=(V+c+R*f²)/(c*f).
```

The argument in [the native alias proof](free_coefficient83_native_alias.md)
applies without alteration: the odd quotient polynomial gives `V=-R mod c`;
the index-4p Pell period modulo f and v=p mod4p give `V=-c mod f`.
The main norm gives `gcd(c,f)=1` and `f²=1 mod c`. Hence the displayed
auxiliary quotient is a positive integer. It restores exactly
`V=c*(auxiliary_quotient*f-1)-R*f²`, and the Pell norm at S gives
`S²V²-(S²-1)y_aux²=1`.

Every one of the 18 supplied witnesses is now a specified positive integer.
The seven factor ports of the actual saved source, in their saved order, are

```
first, main, input, auxiliary, index, transport, scaled strong
  1,      1,     1,         1,     1,         1,       Delta.
```

The complete polynomial is their product minus Delta and is zero. Its main
index is p rather than its computed R. The literal 84 inverse would require
`i=S/(Delta*c²)=1/c`, which is nonintegral. The proof therefore supplies a
full arithmetic wrong-index zero with the displayed necessary-mask interface,
while the exact fixed-recipe exclusions in Section 1 prevent any
universal-language conclusion.

## 6. Executable evidence and its boundary

The fresh helper authenticates the 83 JSON and proof, both scaled-family
notes, and the odd-quotient proof as inert data. No predecessor or archived
Python is imported or executed, and no new polynomial source is emitted.

It checks every small datum in Section 1, the literal packing identity,
input slack, transport congruence, modular Pell residue and noncoprime CRT
coefficient. It also confirms the two stated recipe failures. The value c has
more than `p(p-1)` bits by the elementary bound
`psi_A(p)>2^(p(p-1))`. Materializing that integer, let alone the auxiliary
witnesses, is not part of the evidence.

For a separate complete-graph check, the helper makes 16 signed/rational
assignments through the same triangular formulas, without imposing Pell norms
or positivity. Each executes all 83 paid rows, compares 18 reconstructed cut
values, verifies all seven factor expressions, and checks the entire output
against their product minus Delta. This is 1,328 row evaluations and 288 cut
checks. These finite off-zero tests corroborate the literal formulas; the
general graph substitution and positive-zero theorem are proved above.

Replay from any directory:

```
python3 free_coefficient83_full_arithmetic_alias.py --root ABS_WIP --expect ABS_RECEIPT
```

Checks use explicit exceptions and recursive type-exact receipt comparison.
This packet establishes neither a valid compiler export nor a new universal
arithmetic bound. Soundness of the 83-operation candidate remains open.
