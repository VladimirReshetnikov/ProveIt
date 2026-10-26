# Independent arithmetic audit: unweighted pooling across signed bases

Prepared 25 October 2026 for the current ProveIt research iteration.
This is an AI-assisted independent mathematical review, not external peer review.

## Verdict and precise scope

The proposed two-moment argument is valid under the stated strict framing
hypotheses. It removes the common-sign restriction on the Pell moduli. It also
allows zero bases as syntactically vacuous modulus `-1` blocks, provided the
subsequent semantic bootstrap separately handles or excludes those zero bases.
It does **not** recover a conventional exact power at base zero by itself.

The proof uses no coprimality between distinct moduli. The products of bases
below exist only in the proof and introduce no polynomial coordinates.

## 1. Exact statement

Let `W >= 258` and `A` be integers, with `|A| > W^W`. Put
`b = floor(sqrt(W-1))`, so `b >= 16`. There are at most five base blocks,
and at most seventeen requests in total. Their integer data satisfy

```
|n_j| <= b,   |m_i| <= b,   |k_i| <= b.
```

For each request, the Pell pair `(X_i,Y_i)` is the canonical signed pair
at center `A` and signed index `k_i`. Define

```
T_j = 2 A n_j - n_j^2 - 1,
D_i = m_i - X_i + A Y_i,
delta_i = D_i - n_j Y_i,
H_j = sum_i Y_i (m_i-X_i),
S_j = sum_i (D_i^2-Y_i^2),
E_j = S_j - 2 n_j H_j.
```

The Pell norm gives the exact identity

```
sum_(i in block j) delta_i^2 = E_j - T_j sum_i Y_i^2.       (1)
```

Every `T_j` is nonzero. The following are equivalent:

1. Every old pool condition `T_j | E_j` holds.
2. There is an integer `z` such that

```
sum_j E_j product_(h != j) T_h - z product_h T_h = 0.      (2)
```

Moreover (2) implies `m_i = n_j^(k_i)` as a rational equality for every
nonzero base, and therefore as an ordinary integer equality when `k_i >= 0`.
For `|n_j| >= 2`, integrality forces `k_i >= 0`. For the unit bases, all signed
indices retain their usual unit-power meaning. It also implies `T_j | delta_i`
for every request, including the vacuous zero-base blocks.

## 2. Modulus signs and size

If `n=0`, then `T=-1`. For a nonzero base,

```
|T| >= |n| [2|A|-|n|-1/|n|] >= |n| (2|A|-W),
```

because `|n|+1/|n| <= b+1 <= W`. Also

```
2|A|-W > W^W,
sign(T) = sign(A n),
sign(n T) = sign(A).                                    (3)
```

The last sign, common to all nonzero-base blocks, is what makes the second
moment argument work. No common sign of the `T_j` is needed.

## 3. Clear negative indices before applying a height estimate

Discard all zero-base blocks from the rational sums; they already contribute
integers to `sum E_j/T_j`. Set

```
C = product_(n_j != 0) n_j^b,
L = product_(n_j != 0) n_j.
```

Empty products are one. Both products are nonzero. For a request at nonzero
base `n_j`, set

```
d_i = C m_i - (C/n_j^b) n_j^(b+k_i).                      (4)
```

This is an integer, including for negative indices and negative bases:
`b+k_i >= 0` and `C/n_j^b` is integral. Since `T_j = -1 modulo n_j`,
the residue class of `n_j` is a unit modulo `T_j`. The canonical Pell
congruence therefore gives

```
C delta_i = d_i modulo T_j.                              (5)
```

Equations (1), (2), and (5) prove that the rational number

```
R0 = sum_(nonzero bases j) sum_(i in j) d_i^2/T_j           (6)
```

is an integer. Multiplication by `C^2` is legitimate because it is an
integer; no cancellation or inversion of `C` modulo any modulus is used.

## 4. First height bound: the rational sum vanishes

With at most five nonzero bases,

```
|C| <= b^(5b),
|C/n_j^b| <= b^(4b),
|d_i| <= b^(5b+1)+b^(6b) <= 2 b^(6b).
```

Write `S = sum_i d_i^2`. There are at most seventeen summands, so

```
S <= 68 b^(12b) < W^(6b+1) <= W^W.                       (7)
```

Here `68<W`, `b^2<W`, and `6b+1<=b^2+1<=W` for `b>=16`.
By (3), every modulus in (6) has absolute value greater than `W^W`.
Thus `|R0|<1`; as `R0` is integral, `R0=0`.

This alone would not exclude cancellation between positive and negative
moduli. The following second step is essential.

## 5. Second moment: cancellation is impossible

For every nonzero base, the exact rational identity is

```
2A/T_j = 1/n_j + (n_j^2+1)/(n_j T_j).
```

Consequently `R0=0` implies

```
sum_i d_i^2/n_j + sum_i d_i^2 (n_j^2+1)/(n_j T_j) = 0.    (8)
```

Multiplying the first sum by `L` gives an integer. For the second sum, (3)
implies

```
(n_j^2+1)/|n_j T_j| <= 2/(2|A|-W).
```

Since `|L|<=b^5`, its absolute value after multiplication by `L` is at most

```
2 b^5 S/(2|A|-W) < 1.                                   (9)
```

For a fully explicit verification of the strict inequality,

```
2 b^5 S <= 136 b^(12b+5)
          < W^(6b+4)
          <= W^W
          < 2|A|-W.
```

The middle comparison uses `136<W`, `b^(12b+5)<(b^2)^(6b+3)`,
and `6b+4<=b^2+1<=W` for `b>=16`.

The integer in (8), multiplied by `L`, must therefore be zero. Hence the
second sum in (8) is zero too. Each of its terms has sign `sign(A)` or is
zero, by (3). Its numerator factor `n_j^2+1` is strictly positive. It
follows that every `d_i=0`.

## 6. Exact recovery and converse

Dividing (4) in the rational numbers by the nonzero integer `C` gives
`m_i=n_j^(k_i)`. If `|n_j|>=2` and `k_i=-u<0`, then the equality would imply
`m_i n_j^u=1`, impossible over the integers. Thus all nonunit bases have
nonnegative indices. For the unit bases no index-sign claim is needed.

The canonical Pell congruence now gives `T_j | delta_i`. Identity (1) yields
`T_j | E_j`. For a zero base this divisibility was already automatic because
`T_j=-1`.

Conversely, if all old pool conditions hold, define the integer
`z=sum_j E_j/T_j`. Multiplication by the nonzero product of all moduli gives
(2). This proves the required existential equivalence and permits integral
restoration of each old pool quotient.

## 7. Checks required at the application boundary

- Verify that the inherited frame really bounds every actual base, output,
  and nominal index occurring in these five blocks by `b`.
- Retain the canonical signed Pell-pair theorem before applying this lemma.
  Arbitrary norm-one pairs without authenticated indices do not suffice.
- A zero-base block contributes no power semantics. In the intended
  application, the nonzero early bases must first yield the bootstrap that
  proves `q` and `q+1` nonzero. It is then valid to interpret those blocks.
- Count the actual number of blocks and requests. The inequalities above are
  certified for at most five and seventeen, respectively; larger values need
  a new explicit budget.
- The old quotient restoration is integral on the zero set. It is not a
  globally polynomial inverse map and should not be advertised as one.
- A finite JSON expansion checker authenticates the emitted polynomial but
  does not prove this unbounded arithmetic theorem or the imported ZFC
  calibration.

No arithmetic gap was found in the proposed mixed-sign pooling lemma at this
precise boundary.

## 8. A finite negative control: the height assumption is essential

Take `A=10`, two bases `+1,-1`, and index zero in every request. The canonical
Pell pairs are then `(X,Y)=(1,0)`. At base `+1`, request output `m=4`, giving
`E_+=9` and `T_+=18`. At base `-1`, use three outputs `4,2,2`, giving
`E_-=9+1+1=11` and `T_-=-22`. Thus

```
E_+/T_+ + E_-/T_- = 1/2 - 1/2 = 0.
```

The pooled polynomial vanishes with `z=0`, although `18` does not divide `9`
and `-22` does not divide `11`. These are canonical signed Pell pairs and
bounded integer requests. The failed hypothesis is the sufficiently large
center. This is a concrete counterexample to an unqualified assertion that
mixed-sign pools can always be combined by clearing the denominators.
