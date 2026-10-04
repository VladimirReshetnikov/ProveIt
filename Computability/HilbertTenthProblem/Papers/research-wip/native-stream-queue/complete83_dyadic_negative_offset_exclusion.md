# Conditional dyadic exclusion of the negative common offset

Fix an actual modified compiler from `complete75_half_binomial_compiler.md`, with its full masks and layout, and the complete83 shared-projection source. At any positive zero for which **q is a power of two**, write q=2^t and u=2dx+b. Then:

* If u<t, necessarily W=2^u and X=2^R. The positive integer rho=U/H restores a complete84 positive zero with every other supplied coordinate unchanged.
* If u>=t, the necessary branch is W=0 and X=2^R−2^u. This note does not exclude that branch.

In particular the possible negative value W=2^u−q is excluded on every valid compiler slice. This is a conditional soundness theorem for one branch, not a proof that q is dyadic, not a full soundness theorem for complete83, and not a new universal operation bound. No auxiliary witness or source row is changed.

## 1. Actual source and inherited pretyping

Use the notation of the pinned `complete83_shared_projection_math.md` and its independent mathematical review. Here U is the supplied positive `shared_projection`; the packed index R is the computed `r_lhs`, not a separately supplied integer. The literal source has

```
q=(B−1)J+1,  X=wq,  Y=sq^3,
C=q−F−Z−alpha−2dx,  W=C−Z,  u=2dx+b,
R=(q^2−Z−qF)(q^2−1)+(MC+q(MF0+B−1))J,
D=ac+X+U+sigma H,  mu=a*kappa+W+U.
```

The source port `MF` is MF0+B−1; MF0 denotes the native field mask in this note. The companion helper checks 32 literal interface rows against the authenticated complete83 JSON, without evaluating that source or importing a predecessor helper. Its existing 83=46M+37A, 18-positive-witness ledger is only recounted, not improved.

The accepted offset theorem first establishes the following facts without q being dyadic or H dividing U:

```
q>=16, C>=0, F+Z<q, |W|<q,
R>3q+1, R+2<q^4, R=3 mod4,
0<u<2q<R, v=u,
X−W=2^R−2^u,
r=(R−1)/2, a=Y(X+1),
k=2 psi_P(r+1), c=psi_A(R), Y<c/k<Y+1,
P=2XY^2+1, A=a+2.
```

All supplied coordinates, including x, F, Z, alpha, w and s, retain their original strict-positive domain. The theorem also proves

```
H|U  iff  X=2^R  iff  W=2^u,
```

and gives a positive integral inverse at that equality. No earlier complete84 theorem is invoked for a nonzero-offset tuple.

Now assume q=2^t. Because q−1 is divisible by B−1=2^d−1, the elementary divisibility identity `2^d−1 | 2^t−1 iff d|t` gives t=dN and q=B^N for a positive integer N. This does not infer dyadic q from the repunit equation. Since R>3q+1>t, reduction of the exact offset identity modulo q gives precisely

```
u<t:  W=2^u or 2^u−q,
u>=t: W=0.
```

On the two noncanonical branches, X=2^R−2^ell with ell=t or ell=u respectively. Here ell>=t and ell<R−1. Thus every dyadic branch satisfies X>2^(R−1), including the canonical X=2^R branch.

## 2. The half-binomial extraction still holds

Set

```
xi=(X+1)^(2r)/X^r,
C_j=binom(2r,r+j),
M_r(X)=sum_(j=0)^r C_j X^j.
```

The elementary Pell estimates used in half-binomial42 §5 depend on the exact first/main indices and the size inequalities, not on the equality X=2^R. In the present pretyping domain they give

```
xi/2<c/k<(xi/2)(1+8r/a),
xi<2Y+2, Y>X^r/3, a>X^(r+1)/3,
0<c/k−xi/2<16r/(X+1).
```

The lower estimate comes first: X>=16, r>=24, and 6XY^2>a imply it and then a>8r, so the upper estimate's hypothesis 4r/a<1/2 is established before use. The older kernel's stronger X>=4096 is unnecessary. This is the same order of estimates already checked in the accepted offset note and its evidence companion.

Expand xi=M_r(X)+theta. Since X>2^(R−1)=2^(2r),

```
0<theta=sum_(j=1)^r binom(2r,r−j)/X^j
       <2^(2r−1)/X<1/2.
```

Also 16r/(X+1)<1/2 for r>=24. X is even on all the dyadic branches, so M_r(X) is even: its central coefficient is even and every other term contains X. Consequently

```
M_r(X)/2 < c/k < M_r(X)/2+1/4+1/2 < M_r(X)/2+1.
```

Comparison with Y<c/k<Y+1 proves the exact identity

```
Y=M_r(X)/2.                                             (1)
```

This argument does not assign Y in advance, does not assume the native masks, and does not presume the population threshold being proved below.

For X=2^R−2^ell, ell>=t, put h=3t+1. R>3q+1>h implies X=−2^ell modulo 2^h. Every j>=4 term has valuation at least 4ell>=4t>=h. Hence the retained cubed-scale condition has the exact scalar equivalent

```
q^3 | Y  iff
C_0−2^ell C_1+2^(2ell) C_2−2^(3ell) C_3 = 0 mod 2^(3t+1).   (2)
```

Equation (2) is necessary and sufficient for this divisibility of the already recovered Y. It is not a sufficient condition for a complete83 zero.

## 3. Fixed-layout bounds before native typing

To distinguish the inner radix from the packed index, write V0=2^b. The actual compiler has B=V0^L, d=bL, V0>=16, native exponent set E, maximum Emax, and a designated ignored dummy e_* with e_*+1<Emax. Complete76 §1 and the modified compiler §1 give

```
Dmask=B−1−MC=sum_(e in E,e!=1) V0^e+2 V0^e_*.
```

Start is at exponent0, End at1, and e_*>1. Thus Dmask>=4. Its V0-digits are at most3 and all its nonzero positions are at most Emax. The actual separated layout has L>=Emax+2 (indeed much more), so

```
4<=Dmask<V0^(Emax+1),
Dmask+V0<B−1.                                          (3)
```

For the last strict inequality, use the integer bound Dmask<=V0^(Emax+1)−1 and L>=Emax+2; multiplying the former leading power by V0 leaves a gap larger than V0. These are fixed numeral facts. They do not require supplied Z to be native typed.

Suppose for contradiction that u<t and W=2^u−q. As u=2dx+b and t=dN with 0<b<d, N>=2x+1 and

```
2^u<=q*V0/B.
```

Using J=(q−1)/(B−1), (3) gives

```
Dmask*J+2^u
 <q*(Dmask/(B−1)+V0/B)<q.                              (4)
```

But C=Z+2^u−q>=0. Therefore

```
4<=Dmask*J<Z<q.                                       (5)
```

The crucial order here is scalar layout bound, then C>=0, before any mask typing.

## 4. Packed low residues prevent cancellation

The literal packed-index expression and repunit equation give

```
R = Z+MC*J = Z−Dmask*J−1 mod q.                        (6)
```

Let k2=v2(r+1), l2=v2(r+3), p=popcount(r), with r odd. If k2>=t−1, then R=2(r+1)−1 is −1 modulo q. Equation (6) forces Z=Dmask*J, contradicting (5).

If l2>=t−1, then R=2(r+3)−5 is −5 modulo q. Thus

```
Z=Dmask*J−4 mod q.
```

Because 4<=Dmask*J<q, the first representative is nonnegative and below Dmask*J; adding q makes it at least q. Neither equals the Z in (5). Consequently

```
k2<=t−2 and l2<=t−2.                                  (7)
```

This second exclusion matters. Merely assuming k2<t does not control the third binomial coefficient.

The exact central-binomial identity and the three adjacent-coefficient ratios give, with h2=v2(r−1)>=1,

```
v2(C_0)=p,
v2(C_1)=p−k2,
v2(C_2)=p+h2−k2,
v2(C_3)=p+h2−k2−l2.                                   (8)
```

Indeed C_1/C_0=r/(r+1), C_2/C_0=r(r−1)/((r+1)(r+2)), and C_3/C_0=r(r−1)(r−2)/((r+1)(r+2)(r+3)); r,r+2,r−2 are odd. For the negative-W branch ell=t, (7) makes all three weighted valuations `v2(C_j)+jt`, j=1,2,3, strictly greater than p. Therefore the cubic in (2) has valuation exactly p. Combining (1), (2) and Y=sq^3 proves

```
p>=3t+1, hence popcount(R)=p+1>=3t+2.                 (9)
```

Only the low residues of the actual packed R were used to recover this threshold. No native restriction on Z or F was assumed.

## 5. Native masks now close the contradiction

Use the actual shifted masks, not their unmodified predecessor:

```
S'=(Z−1)+qF,
T_C=MC*J+1, T_F=MF0*J−1, T'=T_C+qT_F,
R=(q^2−S')(q^2−1)+T'.
```

The pretyping raw bounds give 1<=S'<q^2; the complete modified compiler gives 0<T'<q^2−1 and popcount(T')=t+2. The inverse-population lemma in its §2 gives

```
popcount(R)<=3t+2,
```

with equality exactly when S' AND T'=0. Thus (9) forces equality and, in particular,

```
(Z−1) AND (MC*J+1)=0.                                 (10)
```

Within the t-bit word, the complement of MC*J is Dmask*J. MC is even and Dmask*J is odd, so adding the origin bit to MC*J removes precisely that bit from its complement. Equation (10) implies that Z−1 is a bitwise subset of Dmask*J−1, and hence

```
Z<=Dmask*J.
```

This contradicts (5). The negative-W branch is impossible. Therefore, when u<t, the remaining branch is canonical and the accepted offset inverse restores rho=U/H as a positive integer. This completes the stated conditional theorem.

## 6. Evidence and exact scope

The fresh standard-library helper authenticates the eight predecessor files listed in its `PINS`, reads the complete83 JSON as inert data, and guards the 32 displayed interface producers. It does not run an inherited source, import any predecessor helper, or construct a valid-program zero. The finite checks compare complete half-binomial modular sums with the cubic reduction, recompute the adjacent coefficient valuations and guarded unique-central valuation, and check the elementary low-residue exclusion on bounded integer ranges. The receipt records 3,248 complete half-binomial/cubic congruence cases, 16,288 guarded valuation cases, 41,466 residue cases, and a digest of the modular records. Fresh normal and optimized Python (`-O`) exact receipt replays from `/` both pass. These finite checks corroborate the all-integer proofs above; they do not replace them.

One intentionally unguarded example records why (7) is needed: t=4, r=8189=2^13−3 has k2=1<t, p=12 and l2=13. Its four weighted valuations are 12,15,21,12, so central and third terms can cancel. This is a scalar diagnostic only, not a compiler tuple or an extra zero. The valid negative branch excludes it by the packed residue argument.

The read mathematical dependencies are the entire accepted shared-projection note and its review; half-binomial42 §§4–6, especially the quantitative estimates of §5; modified complete75 compiler §§1–3 for the fixed masks and inverse-population lemma; complete76 §1 for Dmask's baseline formula; and complete78 §2 for the separated exponent layout. The companion source note is authenticated and its displayed interface is read. This is not a new audit of the underlying machine-to-window compiler or a replay of its finite evidence.

The unresolved sectors are q not dyadic and u>=t with W=0. In the latter sector formula (2) remains available with ell=u, but this note has not proved the old population threshold or native typing there. In particular the present result does not turn the complete83 candidate into a universal compiler.

The frozen companion hashes are:

* PY `1bfe8166349fbd16b8557c87cccbbe9827f0eb0813c6227858c22a1fb5a32b35`.
* JSON `6231bded06dbd82575414566cf0ddbd63594f2d21529e36a484cb024b4365144`.

Replay the new helper with `--root` set to the native-stream-queue directory and `--expect` set to its new receipt. The mutually exclusive `--output` option creates a fresh receipt with exclusive file creation. No predecessor program is part of either mode.
