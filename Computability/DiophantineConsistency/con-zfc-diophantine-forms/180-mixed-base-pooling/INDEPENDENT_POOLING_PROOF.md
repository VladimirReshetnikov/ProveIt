# Oriented reciprocal pooling for several Pell moduli

Independent proof review, 25 October 2026. This extends the two-base theorem
in package 168. It is a relative arithmetic theorem: a final consistency
claim additionally needs the source equation's established calibration and
the stated canonical-Pell and height hypotheses.

## Theorem

Let `W >= 258`, `|A| > W^W`, and `b = floor(sqrt(W-1))`. Let `n_1,...,n_s`
be arbitrary integers, including zero. Partition `r` requests `(m_i,k_i,X_i,Y_i)` among the
bases. Suppose:

* `n_j^2 < W`, `m_i^2 < W`, and `k_i^2 < W`;
* `(X_i,Y_i)` are the canonical signed Pell coordinates at parameter `A`
  and signed index `k_i`;
* `4r < W` and `(s+1)b+1 <= W`.

The last two bounds hold, in particular, for `s <= 15` and `r <= 64`.
Let `T_j = 2 A n_j - n_j^2 - 1`. For every request put
`D_i=m_i-X_i+A Y_i`, and for block `I_j` put

    H_j = sum_{i in I_j} Y_i(m_i-X_i),
    S_j = sum_{i in I_j}(D_i^2-Y_i^2),
    E_j = S_j-2 n_j H_j.

Then the following three conditions are equivalent:

1. `T_j | E_j` for every block `j`.
2. Every request in a block with `n_j != 0` is the exact signed rational
   power `m_i=n_j^{k_i}`. Zero-base blocks impose no condition.
3. There exists an integer `z` with

    sum_j n_j E_j product_{h != j} T_h - z product_h T_h = 0.       (1)

Whenever `|n_j|>=2`, these conditions also force `k_i>=0`.

No nonzero-base, relative-sign, distinctness, or coprimality hypothesis is
needed. A zero base has modulus `T_j=-1`, so its divisibility condition is
automatic and its oriented term vanishes.

## Proof

For each nonzero base, `n_j^2+1 <= W` gives

    |T_j| >= 2|A||n_j|-(n_j^2+1) >= 2|A|-W > W^W.

Moreover `sign(T_j)=sign(A n_j)`. For zero bases `T_j=-1`. All moduli
are therefore nonzero, and all nonzero rational weights `n_j/T_j` have
sign `sign(A)`.

We will use the slightly stronger weighted denominator estimate

    |T_j|/|n_j| >= 2|A|-(n_j^2+1)/|n_j|
                  >= 2|A|-W > W^W.

Put `delta_i=D_i-n_jY_i` for requests in block `j`. Direct expansion gives

    sum_{i in I_j} delta_i^2 = E_j - T_j sum_{i in I_j}Y_i^2.      (2)

Equation (1), divided by the nonzero product of the moduli and combined
with (2), says that

    Q = sum_j sum_{i in I_j} n_j delta_i^2/T_j

is an integer. Discard zero-base blocks from this sum. If no blocks remain,
all desired divisibilities are automatic. Otherwise let `J` index the
nonzero bases, let `s'=|J|`, and let `C=(product_{j in J} n_j)^b`, a nonzero
integer. For requests in these blocks, `|k_i|<=b` ensures that the number

    d_i=C m_i - (C/n_j^b)n_j^{b+k_i}

is an integer. Canonical Pell coordinates have the congruence

    X_i+(n_j-A)Y_i == n_j^{k_i} (mod T_j).

For negative indices the modular power is well defined because
`T_j == -1 (mod n_j)`. Multiplication by `C` clears those negative powers,
and yields `C delta_i == d_i (mod T_j)`. Consequently

    R = sum_j sum_{i in I_j} n_j d_i^2/T_j

differs by an integer from `C^2 Q`, and is itself an integer.

Every remaining base and request input has absolute value at most `b`. Thus

    |C| <= b^{s' b},
    |C/n_j^b| <= b^{(s'-1)b},
    |n_j^{b+k_i}| <= b^{2b},
    |d_i| <= b^{s' b+1}+b^{(s'+1)b} <= 2b^{(s+1)b}.

It follows that

    sum_i d_i^2
       <= 4r b^{2(s+1)b}
        < W^{(s+1)b+1}
       <= W^W.

Here `b^2<W` gives `b^{2(s+1)b}<W^{(s+1)b}`, and `4r<W`
supplies the remaining factor. The weighted denominator estimate gives
`|R| <= sum_i d_i^2/(2|A|-W) < 1`. Every summand of `R` has
the common sign of `A`, unless its square vanishes. Since `R` is an integer,
`R=0`, and every `d_i=0`. Division by `C` in the rational numbers gives
`m_i=n_j^{k_i}`. If `|n_j|>=2` and `k_i<0`, this identity would give
`m_i n_j^{-k_i}=1`, impossible in integers.

This proves condition 3 implies condition 2. Conversely, condition 2 and
the canonical Pell congruence give `T_j | delta_i` for every request with
nonzero base. Equation (2) then implies `T_j | E_j`. For zero bases
`T_j=-1`, so divisibility also holds. This proves condition 2 implies
condition 1. Finally, condition 1 makes `z=sum_j n_j E_j/T_j` integral
and satisfies (1), proving condition 1 implies condition 3.

Finally `W>=258` gives `b>=16`. If `s<=15` then
`(s+1)b+1 <= 16b+1 <= b^2+1 <= W`, and `r<=64` gives `4r<=256<W`.
This proves the stated uniform corollary.

## Exact elimination of quadratic pooling coordinates

Suppose an existing system stores the two rows

    K_j-2H_j-(2A-n_j)L_j = 0,
    S_j-n_j K_j+L_j = 0

for each of `s` blocks. They are equivalent to `E_j=T_j L_j` together with
the displayed formula for `K_j`. If all `2s` coordinates `K_j,L_j` occur
only in these rows, replace them and the `2s` rows by (1) and its one
coordinate `z`.

The forward witness map is `z=sum_j n_j L_j`. The reverse map is
`L_j=E_j/T_j` and `K_j=2H_j+(2A-n_j)L_j`, which is integral by the theorem.
For zero bases the same formula simply reads `L_j=-E_j`, so restoration
is still integral without interpreting a zero-base power. This proves
equality of projected solution sets under all stated hypotheses.
It eliminates `2s-1` integer coordinates. It is an existential projection,
not a polynomial coordinate bijection.

When `A,n_j` are coordinates, `D_i` uses a retained coordinate `Z_i=AY_i`,
and `H_j,S_j` are evaluated as quadratic expressions, each `T_j` is
quadratic and `E_j` is at most cubic. The new residual has degree at most
`2s+2`, so its squared contribution has degree at most `4s+4`. Substituting
nonlinear expressions for bases or `Z_i` changes this bound and must be
counted from the actual exported polynomial.

## Singleton congruences can be pooled in the same equation

Some source blocks may instead consist of a single request with private
coordinates `T,Q` and rows

    T-(2An-n^2-1)=0,
    delta+TQ=0,               delta=m-X+Z-nY, Z=AY.

Define `H=Y(m-X)`, `S=(m-X+Z)^2-Y^2`, and `E=S-2nH` for that block,
exactly as above. The same weighted equation is equivalent to the original
singleton divisibility condition as well. In the forward direction
`T|delta` and `delta^2=E-TY^2` imply `T|E`. In the reverse direction the
theorem recovers the exact power when `n!=0`, which gives `T|delta` by
the canonical Pell congruence; if `n=0`, then `T=-1` makes divisibility
automatic. Restore `Q=-delta/T` as an integer, and restore `T` by its
displayed formula. Thus singleton blocks and prior two-row aggregate
blocks may be mixed freely in the same pooling theorem. Each block
still contributes two private coordinates, so five such blocks can
replace ten coordinates by one and save nine.

## Congruence proof for every signed parameter and index

For any integer `A`, let `u` be the element `A+v` of
`Z[v]/(v^2-(A^2-1))`. Its inverse is `A-v`, so all integral powers
`u^k=X_k(A)+Y_k(A)v` exist for `k` in `Z` and have integer coordinates.
This is exactly the recurrence with matrix

    [[A,A^2-1],[1,A]],

whose determinant is one. The substitution `v -> n-A` defines a ring
map to `Z/TZ`, because

    (n-A)^2-(A^2-1)=n^2-2An+1=-T.

It sends `u` to `n` and its inverse to `2A-n`; their product is
`n(2A-n)=T+1`. Hence for every signed `k`,

    X_k(A)+(n-A)Y_k(A) == n^k (mod T).

This calculation has no parity hypothesis and works for either sign of
`A`. For the nonzero bases used in the height argument `|T|>W^W>1`,
so the usual residue-ring unit interpretation is unambiguous. At `n=1`
and `n=-1`, negative indices cause no problem: their rational unit powers
are integers and no nonnegative-index conclusion is drawn. At `k=0`,
`(X,Y)=(1,0)`, and exactness simply gives `m=1` for nonzero bases.

## Necessity of orientation

Integrality alone is insufficient if reciprocal weights have opposite
signs. For arbitrary nonzero moduli the elementary example
`1/2+1/(-2)=0` already defeats the inference that every square numerator
vanishes. Multiplication by the corresponding base gives the required
common sign for the Pell moduli. This example is a warning about the
sign argument, not a purported canonical-Pell counterexample to a
particular unweighted source equation.

## Bootstrap caution

The equivalence of projected solution sets does not require any nonzero-base
bootstrap. Restore the old pooling coordinates first, then apply the
parent's existing semantic proof, including its own proof that its relevant
bases are nonzero. This avoids introducing circular dependencies.

The retained equations must still establish canonical Pell coordinates,
square-frame bounds, and the strict-height hypothesis before this argument.
A graph-level variable count is not a proof of those arithmetic prerequisites.
