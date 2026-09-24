# A grouped, exact arithmetic interface for a periodic Life preimage

This is an original interface construction, not a smaller universal
certificate. It assumes a separately proved packed-Boolean predicate and
accounts separately for the geometry, zero-valued fields, and the repeated
target. The finite existential semantics are those in
[the periodic-preimage audit](EXPLORATION_LIFE_PERIODIC_PREIMAGE.md).

## 1. Geometry and conventions

Fix radix `B=64`. Let the torus have width `m>=1` and height `n>=1`, and put

```
W=B^m, Q=W^n, A=W/B, h=(Q-1)/(W-1).
```

A word packs cell `(i,j)` at exponent `i+m*j`. A Boolean word has exactly
`m*n` base-64 digits, each zero or one. The first- and last-column masks are
`h` and `A*h`. The word `C` is the preimage, `Y` is the target, and
`U1,...,U5` are Boolean local auxiliary words.

All nine neighbor positions retain their multiplicities when a dimension
is one or two. The formulas below therefore describe the infinite periodic
extension, including these cases.

If a surrounding arithmetic kernel has already proved `Q` is a power of
two, the following six primitives and four free equality tests establish
this geometry:

```
wm1=W-1; qm1=Q-1;
hwm1=h*wm1;        hwm1=qm1;
wquot=W*quot;      wquot=Q;
sixtythree=63*d;   sixtythree=wm1;
a64=64*A;          a64=W.
```

Here `W,Q,h,quot,d,A` are positive. The second equality makes `W` a power
of two. Since the order of 2 modulo 63 is 6, the third makes `W=64^m`
with `m>=1`. The first, together with `Q` a power of two, makes `Q=W^n`:
`2^a-1` divides `2^b-1` precisely when `a` divides `b`. The last defines
the positive last-column shift `A`.

This is **4 multiplications and 2 additions/subtractions**. The power-of-two
kernel itself is not included. No variable power is treated as a free
literal.

## 2. Exact first and last column extraction

Use nonnegative words `L,R,Xl,Xr`, and impose

```
C+h   = Xl+2L,
C+A*h = Xr+2A*R.                                      (1)
```

Require `C,Xl,L,Xr,A*R` to be Boolean words of length `m*n`. Each side
of either equation has digits in `0..2`, so no base-64 carry is possible.
Consequently

```
L   = sum_j c[0,j] W^j,
A*R = sum_j c[m-1,j] A W^j.
```

Thus `R` is the last-column word shifted to the first-column positions.
Its own Booleanity follows from the displayed identity; it need not be
tested in addition to the Booleanity of the computed word `A*R`.

Both edge checks together cost **4 multiplications and 4 additions**,
including the product `A*h` and the product `A*R`.

There is a real obstruction to replacing (1) by a single apparently
cyclic equation with an arbitrary column-supported quotient. With two
rows, `W=64^2` and `C=64^3`, both

```
E=W, R=W       and       E=1, R=1+W
```

satisfy `64*C=E+(W-1)R`. In both cases `E,R` are Boolean and `R` is
supported on first-column positions. Only the first is the rowwise
rotation. The second moves the occupied cell to a different row. A
column-support assertion alone therefore does not identify an edge.

## 3. Combine all eight neighbors without supplying their planes

Let `H` denote, for the proof only, the rowwise cyclic horizontal triple:
left neighbor plus center plus right neighbor. Its digits are in `0..3`.
The exact integer identity is

```
64 H = 4161 C + (W-1)(L-64R),                          (2)
```

because `4161=64^2+64+1`. This includes the row wrap at both ends.

Set `K=W^2+W+1`. Let `Vtrue` be the inclusive 3-by-3 torus sum, whose
digits are in `0..9`. Whole-row rotation is multiplication by `W` modulo
`Q-1`, so

```
K H = W Vtrue (mod Q-1).                               (3)
```

The four corner neighbors are present because horizontal and vertical
torus rotations commute. A separate corner constraint is unnecessary.
Only vertical rotation is replaced by ordinary modular reduction. No
helical row-major rotation is substituted for horizontal wrap.

For Boolean `b,y,u1,...,u5` and `0<=N<=8`, direct enumeration gives

```
N+22y+6(u1+u2-b)+7u3 = 11u4+14u5                     (4)
```

for some five auxiliary bits if and only if `y` is the Life output with
center `b` and neighbor sum `N`. Move the center into the inclusive sum:

```
V = 11U4+14U5-22Y-6(U1+U2)+7(C-U3).                   (5)
```

The complete neighbor and local-rule check is one integer congruence:

```
K*[4161C+(W-1)(L-64R)] = W*(64V) + z*(Q-1),           (6)
```

where `z` is an unrestricted integer. Neither `H`, `Vtrue`, nor the eight
neighbor words are supplied. The signed temporary `64V` is evaluated
with the free scalar coefficients `704,896,1408,384,448`, so scaling
it introduces no additional arithmetic operation.

### Why the congruence is sufficient

By (1)-(3), (6) says

```
64W*(V-Vtrue)=0 (mod Q-1).
```

Both `64` and `W` are coprime to `Q-1`. Each coefficient of (5) lies in
`[-41,32]`, whereas each coefficient of `Vtrue` lies in `0..9`.
Thus `V-Vtrue` has coefficients in `[-50,32]`, and

```
abs(V-Vtrue) <= 50*(Q-1)/63 < Q-1.
```

Its divisibility by `Q-1` forces the integer to be zero. Moreover, an
integer polynomial at 64 with every coefficient between -50 and 32 can
equal zero only if every coefficient is zero: reduce modulo 64 and
induct after removing the constant coefficient. This yields (4) at
every cell, with its actual neighbor count. The separately verified
local truth table then yields the required Life update.

Conversely, a valid torus preimage gives (1), one valid five-bit local
witness at every cell, and an integer `z` by (2)-(3). This proves both
directions under the stated Boolean-word and geometry conditions.

## 4. Exact counted schedule

The following schedule assumes `W-1,Q-1,A,h` from Section 1 and the
eleven nonnegative inputs

```
C,Y,U1,U2,U3,U4,U5,L,R,Xl,Xr
```

plus the signed input `z`. The three equality tests are free.

| Step | Primitive |
|---:|---|
| 1 | `rightmask=A*h` |
| 2 | `leftsum=C+h` |
| 3 | `lefttwo=2*L` |
| 4 | `leftout=Xl+lefttwo`; test `leftsum=leftout` |
| 5 | `rightsum=C+rightmask` |
| 6 | `rightedge=A*R` |
| 7 | `righttwo=2*rightedge` |
| 8 | `rightout=Xr+righttwo`; test `rightsum=rightout` |
| 9 | `br=64*R` |
| 10 | `edge=L-br` |
| 11 | `correction=(W-1)*edge` |
| 12 | `centerconv=4161*C` |
| 13 | `horizontalnumerator=centerconv+correction` |
| 14 | `W2=W*W` |
| 15 | `K0=W2+W` |
| 16 | `K=K0+1` |
| 17 | `conv=K*horizontalnumerator` |
| 18 | `u12=U1+U2` |
| 19 | `term12=384*u12` |
| 20 | `centerthird=C-U3` |
| 21 | `term7=448*centerthird` |
| 22 | `termY=1408*Y` |
| 23 | `term4=704*U4` |
| 24 | `term5=896*U5` |
| 25 | `rhs45=term4+term5` |
| 26 | `v0=rhs45-termY` |
| 27 | `v1=v0-term12` |
| 28 | `V64=v1+term7` |
| 29 | `WV64=W*V64` |
| 30 | `quotient=(Q-1)*z` |
| 31 | `rhs=WV64+quotient`; test `conv=rhs` |

The schedule costs **31 operations: 16 multiplications and 15 additions
or subtractions**. Together with the six geometry primitives this is
**37 operations: 20 multiplications and 17 additions or subtractions**,
conditional on the eleven Boolean assertions and the proof that `Q` is
a power of two.

The eleven Boolean words are `C,Y,U1,...,U5,L,Xl,Xr,rightedge`. In
particular, the number of Boolean fields has increased from the six
fields of a local-only relation to eleven. Their packing and Booleanity
certificate are not included in 37. This prevents interpreting the
number as a complete inverse-Life verifier or a universal bound.

### A completely explicit positive-witness adapter

Any of the eleven nonnegative inputs can vanish on a valid torus.
Encode each as `value=positive_value-1`, at a cost of eleven subtractions.
Encode `z=zplus-zminus`, where both are positive, at one more subtraction.
All signed intermediates are permitted integer certificate registers;
a subtraction can be checked by reversed addition.

This generic adapter yields **49 operations: 20 multiplications and
29 additions/subtractions** for the same geometry and local interface,
with all thirteen replacement inputs positive. The six geometry inputs
were already positive. The adapter is an honest sufficient cost, not
an optimality claim. A surrounding packed predicate might absorb some
of its shifts, but that would need a new counted construction. No claim
that an arbitrary edge row or auxiliary Boolean plane is nonzero is used.

## 5. Repeating the target is a separate arithmetic obligation

For a target of fixed width `a` and fixed height `b`, let its row words
be `p0,...,p[b-1]` in radix 64 and put `T=64^a`. For this fixed target
shape, `T-1` is a fixed numeral. Define positive repeaters `G,J` by

```
(T-1)G=W-1,
(W^b-1)J=Q-1.
```

The first forces `a|m`. The second forces `b|n`. If

```
P(W)=p0+p1 W+...+p[b-1] W^(b-1),
Y=G*P(W)*J,                                           (7)
```

then `Y` is exactly the target repeated over the witness torus. All
digits remain Boolean: the first repeater occupies disjoint blocks
within each row, and the second occupies disjoint blocks of `b` rows.

Without reusing powers elsewhere, a chain of `ell(b)` multiplications
for `W^b`, Horner evaluation for `P(W)`, the two repeater equations, and
the two products in (7) cost

```
ell(b)+b+3 multiplications and b additions/subtractions.
```

This is a precise fixed-shape upper bound, not a uniform bound for an
arbitrary target input. The variable `W` is not a fixed numeral, so
`W^b` and evaluation at `W` cannot be silently precomputed in the index.
If the target is supplied as one integer at radix `64^a`, converting
its row expansion to radix `W` remains an explicit radix-conversion
problem. The raw integer query-to-target reduction is also unpaid.

Restricting the witness width to the input target width would avoid
this conversion but destroy the unbounded finite-preimage interface:
a fixed-width strip has only finitely many row states. Likewise, a
single global cyclic shift of the packed word gives a helical quotient,
not the required two-dimensional torus.

## 6. Verification and scope

[The exact regression](../verification/explore_life_torus_convolution.py)
checks the local relation's 36 center/count/output cases, exhaustively
checks every Boolean torus presentation with width and height at most
three, checks all eight neighbor positions independently in physical
coordinates, evaluates all 31 primitive statements, and verifies the
two false-edge witnesses above. Its receipt is
[the adjacent JSON](../verification/explore_life_torus_convolution.json).

The finite checks corroborate the proof. They do not certify the omitted
Booleanity, period-growth, raw-target, or uniform encoding mechanisms.
The concrete result is a correct separable torus relation with seven
free equality tests including geometry, and a counted positive-domain
adapter, ready for further optimization.
