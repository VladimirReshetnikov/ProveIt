# Signed comparison coordinates in a Pell index certificate

23 October 2026. This is the exact strengthening used in the released batched power graph. The main Pell coordinates X,Y and the bases A,B remain positive. Only the comparison coordinates S,R, and hence their progression quotients, are allowed to be arbitrary integers.

## 1. Statement

For an integer base `a>=2`, write X_j(a),Y_j(a) for the natural Pell sequence

```
X_0=1, Y_0=0,
X_(j+1)=a X_j+(a^2-1)Y_j,
Y_(j+1)=X_j+a Y_j.
```

Let A,B,X,Y,U,k be natural numbers and V,S,R integers. Assume

```
A>=2, B>=2, X>=1, U>=2, 1<=k<=Y,
X^2-(A^2-1)Y^2=1,
U^2-(A^2-1)V^2=1,
S^2-(B^2-1)R^2=1,
V!=0, Y^2 divides V,
B == 1 (mod 4Y), B == A (mod U),
S == X (mod U), R == k (mod 4Y).
```

Then

```
X=X_k(A), Y=Y_k(A).
```

There is no sign hypothesis on S or R. Since U>=2, its norm already implies V!=0, so the separate nonzero assumption is redundant in the batched implementation.

## 2. Exact standard lemmas used

These are the actual mathematical statements in the primary source `Mathlib/NumberTheory/PellMatiyasevic.lean`, blob SHA `db9c757dd7cac29260397150fd190d72715ea3f8`, read directly for this proof:

<https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/PellMatiyasevic.lean>.

1. **Pell classification** (`eq_pell`). Nonnegative solutions of `x^2-(a^2-1)y^2=1` at a>=2 are exactly `(X_j(a),Y_j(a))`, for j>=0.
2. **Index bound** (`yn_ge_n`). `Y_j(a)>=j`.
3. **Monotonicity** (`strictMono_y`). Y_j(a) is strictly increasing in j.
4. **Squared-divisibility extraction** (`dvd_of_ysq_dvd`). `Y_i(a)^2 | Y_n(a)` implies `Y_i(a)|n`.
5. **Abscissa residue classification** (`modEq_of_xn_modEq`). For `0<i<=n` and any h>=0,

   ```
   X_h(a) == X_i(a) (mod X_n(a))
       implies
   h == i (mod 4n) OR h+i == 0 (mod 4n).
   ```

   The hypothesis is `i<=n`, not `i<n`. Thus the endpoint i=n is explicitly included.
6. **Half-period sign change** (`xn_modEq_x2n_add`). For n,h>=0,

   ```
   X_(h+2n)(a)+X_h(a) == 0 (mod X_n(a)).
   ```

7. **Base congruence transfer** (`xy_modEq_of_modEq`). If a==b mod c, the respective X_j and Y_j coordinates are congruent modulo c for every j.
8. **Base-one reduction** (`yn_modEq_a_sub_one`). `Y_h(b)==h mod(b-1)`. In particular, if b==1 mod M, then `Y_h(b)==h mod M`.

No formalization of the strengthened signed theorem itself is claimed. The short ordinary proof below derives it from these precise lemmas. All statements concern finite integer arithmetic and their proofs are formalizable in ZFC.

### An explicit explanation of squared-divisibility extraction

The fourth lemma is particularly useful for preventing a hidden modulus gap. Write Y=Y_i(A), X=X_i(A). If `Y|Y_n(A)`, division of n by i and the addition formula show that i divides n: writing n=iq+s,0<=s<i, the congruence

```
Y_n(A) == X_(iq)(A)Y_s(A) (mod Y)
```

has a multiplier coprime to Y. Hence `Y|Y_s(A)`; strict monotonicity forces s=0. Write n=iq. Expansion of `(X+Y sqrt(A^2-1))^q` gives

```
Y_(iq)(A) == q X^(q-1) Y (mod Y^2).
```

Thus `Y^2|Y_n(A)` implies `Y|q X^(q-1)`. Pell's norm gives gcd(X,Y)=1, so Y divides q and consequently Y divides n. This argument does not require Y to be prime or any coprimality between the different seed ordinates.

## 3. Proof of the signed theorem

Classify the three norm solutions. There exist indices i,n,h>=0 and signs epsilon,delta in {+1,-1} such that

```
X=X_i(A), Y=Y_i(A),
U=X_n(A), |V|=Y_n(A),
S=epsilon X_h(B), R=delta Y_h(B).
```

This allows independent signs on S and R. When R=0 either choice of delta is harmless. In fact the given congruence and 1<=k<=Y rule out R=0, but that exclusion is not needed yet.

Because Y>=k>=1, i>0. Because V!=0, n>0. The positive divisibility `Y^2 | |V|` gives `Y<=|V|`, and strict monotonicity therefore gives i<=n. Squared-divisibility extraction gives the crucial stronger statement

```
Y divides n.                                              (1)
```

### Step A: the signed abscissa determines h modulo 2n

The base congruence B==A mod U gives

```
X_h(B) == X_h(A) (mod U).
```

Together with S==X mod U, this implies

```
X_h(A) == epsilon X_i(A) (mod X_n(A)).
```

If epsilon=+1, the standard abscissa residue classification immediately yields `h==+i or -i mod4n`, hence also modulo2n.

If epsilon=-1, the half-period identity gives

```
X_(h+2n)(A) == -X_h(A) == X_i(A) (mod X_n(A)).
```

Apply the same residue classification to h+2n. Reducing its conclusion modulo2n removes the shift. In both cases,

```
h == +i or -i (mod 2n).                                  (2)
```

This step remains valid when i=n. Then the target residue X_i modulo X_n is zero; the standard theorem still applies, and the signs coincide as congruence classes where appropriate. No division by X_i, U, or a residue is performed.

### Step B: the signed ordinate determines h modulo 2Y

From B==1 mod4Y and base-one reduction,

```
Y_h(B) == h (mod 4Y).
```

Since R=delta Y_h(B) and R==k mod4Y, we have

```
h == delta k (mod 4Y), hence modulo2Y.                    (3)
```

By (1), 2Y divides 2n, so (2) also holds modulo2Y. Combining (2) and (3) gives

```
i == +k or -k (mod 2Y).                                  (4)
```

### Step C: the short interval resolves both signs

The standard bound Y_i(A)>=i and the assumed k<=Y give

```
1<=i<=Y, 1<=k<=Y.
```

If the plus case of (4) holds, the integer i-k has absolute value less than2Y, so it is zero. If the minus case holds, i+k is a positive multiple of2Y and lies in `[2,2Y]`. Hence i+k=2Y; as each summand is at mostY, both must equalY. This again gives i=k.

Thus X=X_k(A),Y=Y_k(A), as required.

The boundary Y=1 is included: the short interval contains only i=k=1. The possible h=0 case cannot satisfy (3), because 0<k<=Y<4Y. The proof also covers U=2 whenever the remaining assumptions are satisfiable; it never assumes that U is odd. Oddness is needed only in the separate CRT completeness construction, where it is deliberately ensured.

## 4. Exact change to the batched certificate

Keep all other definitions from `BATCHED_PELL_THEOREM.md`. For every seed index use

```
S=X+U*s, R=k+4Y*r,
```

with s,r now **unrestricted integers**. These definitions still supply exactly the two congruences required by the signed theorem. The common norm, the factor V=4P^2*v, and U>=2 supply all its remaining hypotheses. Hence soundness is unchanged.

Completeness is immediate from the already established batched construction, which supplies nonnegative s,r and therefore also supplies unrestricted integer s,r. No new witness-selection premise is introduced.

Each seed therefore loses two nonnegativity requirements. In the released integer quartic compiler each natural semantic coordinate would receive three additional square witnesses, so this removes six integer variables per seed. For sixteen seeds the saving is96 integer variables. The polynomial identity audit and the actual emitted variable count verify this compiler-specific number; the theorem itself is independent of a particular nonnegativity encoding.

## 5. Verification scope

The independent symbolic graph audit checks that the emitted s,r slots are unrestricted, that X,Y still have their necessary natural lower-bound parameterizations, that the exact S,R progressions are present, and that all norms and congruences match the theorem. Mutation controls remove necessary X/Y guards or alter the actual equations. Adding a superfluous sign guard to s or r would preserve the mathematical relation but lose the advertised variable saving; it is rejected as a mismatch to the intended emitted graph, not presented as a logical counterexample.

Finite checks include all four sign combinations in explicit Pell certificates, the endpoint i=n with Y=1, and a finite sweep of the signed-abscissa residue implication. These checks support the implementation; the universal result is proved in Sections2-3.
