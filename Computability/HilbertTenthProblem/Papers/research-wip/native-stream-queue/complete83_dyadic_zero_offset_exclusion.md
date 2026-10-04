# Excluding the dyadic W=0 branch of shared-projection83

Fix the actual modified universal-compiler constants. No positive zero of the unchanged shared-projection83 source can have both dyadic q and W=0. Together with the earlier negative-offset exclusion, this proves that every dyadic positive zero is canonical: X=2^R, W=2^u, and its supplied shared projection U is a positive integer multiple of H. Thus the parent84 chart is recovered on every dyadic zero. The unconstrained83 source is still not proved universal: even, non-dyadic q remains outside this result.

The decisive vertical argument was developed jointly by root and Tesla, with independent challenges from Pascal and Aristotle recorded separately. It uses the partial signed-transport theorem, not the old marker-bijection theorem or an assumption that the signed field equals the old positive field. No operation or witness is added, removed, or counted by this proof-only restriction.

## 1. Exact inputs from partial decoding

Suppose for contradiction that a positive zero has q=B^N, W=0, with B=V^L, V=2^b and d=bL. The dyadic native-mask theorem and the signed-transport partial-recovery theorem give:

* C=Z is a native typed word, containing the origin Start selector and no End selector;
* every cell selects one genuine allowed three-by-three window, and all its tile-copy digits equal that window's one-hot indicators;
* 2^R*C modulo(q−1) is a whole-cell rotation B^h*C with0<h<N;
* the negative word is V*B^(2x)*C modulo(q−1);
* every vertical parity test of the original mask remains present;
* the supplied field is obtained by cyclic subtraction with binary borrows beta in{0,1}.

Horizontal overlap was also proved in the partial theorem, but the contradiction below only needs its consequence that every cell is occupied. We do not assume vertical overlap.

Let a0 be the actual finite tile-alphabet size. The literal Start window from complete81 Section1 has top row H,H,H. Moreover a0>=3: the horizontal boundary tile H, a headless initialization tile I, and the initialized head tile Q are distinct. This argument does not depend on the numerical label assigned to H.

Tile-copy exponents in each cell are exactly

```
e(r,c,s)=T0+(2−r)*3a0+(2−c)*a0+s,
T0=k+3a0, 0<=r,c<=2, 0<=s<a0.
```

The six tested vertical blocks are therefore one contiguous interval

```
[T0+3a0, T0+9a0−1],
```

in increasing-exponent order

```
(r,c)=(1,2),(1,1),(1,0),(0,2),(0,1),(0,0).       (1)
```

No selector, dummy, or anchor lies in this interval. At a target e(r,c,s), the unshifted positive contribution is exactly the center's(r+1,c,s) copy. The aligned positive rotation supplies the temporal cell's(r,c,s) copy. The complete78 coefficient audit and complete76's high-monomial separation exclude every other positive contribution there. Thus its positive digit P is in{0,1,2}, and over each block of a0 digits,

```
sum P = 2.                                        (2)
```

The negative digit reads the negative-predecessor cell at exponent e(r,c,s)−1, because the multiplier is exactly V times a whole-cell rotation. Throughout all six tested blocks, these predecessor exponents are tile-copy positions, from T0+3a0−1 through T0+9a0−2. In particular every negative digit n belongs to{0,1}; the upper ignored dummy bit is absent from this entire interval.

## 2. Passing a vertical test cannot create a borrow

For a tested digit, write beta for the incoming borrow and beta' for the outgoing one. The subtraction identity is

```
f=P−n−beta+V*beta',
0<=f<V, P in{0,1,2}, n,beta,beta' in{0,1}.
```

The retained least-bit test says f is even. Since V is even,

```
P = n+beta mod2.                                  (3)
```

If beta=0, a new borrow would require P=0,n=1, but this has odd output V−1 and fails. Thus beta=0 implies beta'=0 at every passing target.

If beta=1 and the outgoing borrow remains1, then P−n−1<0. Combining this with(3) leaves only P=0,n=1, which produces f=V−2. Therefore a borrow can persist through a passing digit only where n=1. At a passing digit with n=0, it must stop. These elementary facts hold regardless of the source of the incoming borrow.

## 3. The first block resets the borrow; later blocks have even negative weight

In any tested block, the shifted negative one-hot vector has at most two nonzero digits: a possible last-symbol contribution from the immediately preceding tile block, and at most one shifted contribution from its own tile block. Since a0>=3, the first tested block contains a digit with n=0.

If every test passes, Section2 forces any incoming borrow to stop at or before this digit. A passing digit cannot restart a stopped borrow. Thus the borrow is zero **by the end** of the first block, and remains zero throughout all five later tested blocks. No claim of stopping strictly before the first block's last digit is needed.

For each of those later blocks, summing(3) with beta=0 and using(2) gives

```
sum n = 0 mod2.                                   (4)
```

Let delta_g be1 when the negative-predecessor cell's tile in block g has the last numerical alphabet label a0−1, and0 otherwise. Shifting the one-hot vector by one position removes its own last-label bit from the block and admits the preceding block's last-label bit. Hence exactly

```
sum n in block g = 1−delta_g+delta_(g−1).          (5)
```

This identity includes both endpoints and uses no assumption about the label of H.

## 4. Start's constant top row gives a contradiction

Whole-cell rotation by B^(2x) is a permutation of the N cells, whether or not2x is smaller than N. Choose the cell whose negative predecessor is the origin Start window. In its last three tested blocks, corresponding to Start's top row in(1), the negative-predecessor tiles are H,H,H. Their last-label indicators therefore agree.

In particular, for each of the last two tested blocks, equation(5) gives

```
sum n = 1−delta_H+delta_H = 1.
```

Both blocks lie after the first tested block, so(4) requires their negative weights to be even. This contradiction excludes W=0 on every dyadic positive zero of the actual compiler slice.

The argument is local to six contiguous arithmetic test blocks, after the independently established partial decoding. It does not recover a vertical space-time history, need an End window, or appeal to the ordinary-input semantic marker theorem.

## 5. Consequence for every dyadic zero

At every valid positive shared83 zero, the accepted offset theorem gives

```
X−W=2^R−2^u, |W|<q, X=wq, 0<u<R.
```

If q=2^t and u>=t, reduction modulo q forces W=0; Section4 excludes this case. If u<t, the only possibilities are W=2^u or W=2^u−q. The already proved dyadic negative-offset theorem excludes the latter. Therefore every dyadic zero satisfies

```
u<t, W=2^u, X=2^R.
```

In the following identities, H_Pell=4a_Pell+3 is the Pell modulus, distinct from the boundary tile H used in Section4. Set A_Pell=a_Pell+2 and E_u=chi_(A_Pell)(u)−a_Pell*psi_(A_Pell)(u). The accepted source-aligned offset identity is

```
U=E_u−W, E_u−2^u=H_Pell*rho0, rho0 a positive integer.
```

Thus U=H_Pell*rho0. Replacing the supplied shared projection by the positive parent witness rho=rho0 gives the literal inverse to the parent84 substitution U=rho*H_Pell, with all other common supplied coordinates retained. The parent source and its established ordinary-input theorem apply to this restored tuple. Conversely every parent zero gives a shared83 zero by the positive forward substitution and has the inherited dyadic radix.

This is a conditional soundness theorem for the dyadic sector, not a paid dyadic guard. The source still supplies no new proof that q must be a power of two. The even-radix boundary excludes odd q, so the sole remaining noncanonical radix sector is even and non-dyadic. The earlier non-dyadic scalar diagnostic was not a valid-compiler counterexample; its scope is unchanged.

## 6. Exact scope of the fresh evidence

The companion helper authenticates the unchanged source and the exact prerequisite prose; it does not execute any of them. Its fresh finite evidence independently enumerates the local passing-borrow table, all one-hot block transitions for several alphabet sizes, and complete six-block relaxed systems whose final three negative tiles are equal. The positive pair of one-hot vectors is allowed to vary freely at each block, so this finite test does not assume additional tableau consistency. It also checks the literal contiguous-block and predecessor-index formulas.

These checks corroborate the all-alphabet proof in Sections2–4. They are not full native-zero computations, full compiler enumerations, or a global minimum argument. The source remains83=46M+37A with18 positive witnesses as previously counted; this theorem changes no source row and claims no new unconstrained universal operation bound.
