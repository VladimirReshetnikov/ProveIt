# A factored first norm gives a complete 86-operation universal polynomial

The established complete universal construction can be evaluated in
**86 = 48M+38A operations**, with **19 strictly positive existential
witnesses** and exact degree **179**. Its ordinary-strong alternative costs
**87 = 47M+40A**, with the same witness count and exact degree **135**.
The separate 75-operation comparison-system bound is unchanged.

The change replaces a six-operation first norm by a five-operation norm.
It supplies the ordinary positive Pell root rather than its positive gap.
Every other factor, the complete input loader, both ratio slacks, packed
mask conditions, full strong equation and final product-minus-one are
retained from the [asymmetric-scale parents](complete75_asymmetric_scale_tradeoffs.md).
This is a reduction of those complete universal polynomials, not a local
component cost or a fixed-horizon example.

## Exact statement and inherited program interface

For every recursively enumerable set S of positive integers, the same
effective fixed-numeral recipe as the parent yields a polynomial whose
strictly positive witness solutions exist exactly for ordinary positive
input x in S. The numerical program constants are unchanged. In the literal
source their six ports are `Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF`,
with the same precomputed meanings and restrictions as the parent. A use of
a fixed numeral in a binary arithmetic operation is still charged.

The new positive witness list is

```
Jrep,F,alpha,zplus,f,h,i,j,o,s,w,tau_root,eta,zeta,y_aux,Z,delta,rho,sigma.
```

Only `tau_root` is a new name and coordinate interpretation; it replaces
the parent's `tau_gap`. No new witness, fixed parameter, equality or promise
on the ordinary input is introduced. This is the existing fixed-program
universality contract; the construction does not purport to encode the
program in a new single scalar parameter.

The [emitter/checker](complete86_factored_first_root.py) authenticates the
complete parent JSON and five relevant source/receipt dependencies before
reading the literal sources. It imports no historical compiler module.
The [receipt](complete86_factored_first_root.json) contains both complete
new circuits, witness lists, arithmetic ledgers and verification results.

## Polynomial coordinate identity

Retain the actual parent definitions

\[
q=(B-1)J+1,\quad X=wq,\quad Y=sq^3,\quad E=XY,\quad
k=\eta+\zeta,\quad L=E(kY)=XY^2k.
\]

In source names, `L=first_root_base=UM*ksn2` and `k=R10b`.
The old first factor, in its positive gap g, is

\[
N_0(g)=g^2+L(2g-k).
\]

Supply a positive root T instead, and set

\[
\boxed{N'_0(T)=T^2-L(L+k).}
\]

Since L is independent of the first-root coordinate, the integer polynomial
maps

\[
T=L+g,\qquad g=T-L
\]

are inverse on the complete integer coordinate spaces, keeping all other
coordinates fixed. The exact factor identities are

\[
N'_0(L+g)=g^2+L(2g-k),\qquad N_0(T-L)=T^2-L(L+k).
\]

The old gap has no consumer outside its own square and doubling in the
first-norm block. Thus the other seven factors are independent of g and T.
Writing them as N1,...,N7, the full new polynomial is

\[
F_{\rm new}(x,T,\mathbf z)=N'_0(T)\prod_{r=1}^7N_r-1
                         =F_{\rm parent}(x,T-L,\mathbf z).
\]

This is an all-value coordinate identity over the integers or rationals,
not equality at identically named supplied tuples. The factorization is
also the ordinary Pell form: if V=XY², then
`L(L+k)=V(V+1)k²`. Neither V nor L+k is supplied as a free port.

## Full positive-zero bijection

On every positive parent tuple, L is a positive integer and k=eta+zeta≥2.
The forward map T=L+g therefore preserves positivity even away from zeros.
The full coordinate identity takes every positive parent zero to a new one.

Conversely, let every supplied coordinate of the new polynomial be a
positive integer and suppose its complete output is zero. The full
integer product equals one, so each integer factor is a unit. In particular
`N'_0(T)=epsilon`, where epsilon is either −1 or +1. Hence

\[
T^2-L^2=Lk+\epsilon\ge Lk-1\ge1.
\]

Both T and L are positive, so T>L, and the restored gap g=T−L is a
strictly positive integer. All other supplied coordinates were unchanged.
The complete polynomial identity now gives a positive zero of the selected
parent. Its already proved universal soundness theorem applies to that
same tuple and ordinary input. The two maps are inverse on the **full
positive integer zero sets**, including all nineteen witness coordinates.

This proof does not first assume a legal computation, recovered exponent,
typed mask, ratio theorem or positive sign of the first norm. It needs no
new negative-Pell obstruction. Those deeper facts transfer only after the
old positive zero has been restored. It uses integrality of every factor,
positivity of T and L, and Lk>1; it is not a real-witness argument.

The inverse map does not preserve the whole positive orthant. For instance,
take the fixed-numeral fixture in the receipt and set every new input and
witness to one. Then T=1<L, so the restored gap is negative; the complete
polynomial is nonzero. The receipt records this actual full-source
off-zero boundary instead of asserting an unrestricted positive-coordinate
equivalence.

## Five fully paid operations replace six

The old block, with E, kY and k already paid elsewhere, is

```
g2 = g*g
L = E*(kY)
two_g = g+g
gap = two_g-k
cross = L*gap
N0 = g2+cross
```

It costs 3M+3A. The new block is

```
T2 = T*T
L = E*(kY)
next = L+k
product = L*next
N0 = T2-product
```

It costs 3M+2A. All inputs to this block remain live paid registers of the
actual parent. There is no runtime computation of g=T−L or T=L+g; those are
proof maps between the two supplied-coordinate systems. Every surviving
binary addition, subtraction and multiplication costs one, including
nonunit fixed-coefficient uses, all seven final factor multiplications and
the final subtraction of one.

| Full source | Parent M+A | New M+A | New operations | Exact degree | Positive witnesses |
|---|---:|---:|---:|---:|---:|
| Normalized strong equation |48+39=87|48+38|86|179|19|
| Ordinary strong equation |47+41=88|47+40|87|135|19|

As one-comparison arithmetic certificates, these same circuits omit only
the last subtraction and cost 85/86 operations. They do not improve the
separate multi-equation certificate bound of 75. The normalized and ordinary
forms each inherit their own parent's zero-set theorem; no bijection between
the two strong treatments is asserted.

## Exact degree and the operation/degree tradeoff

Let Q=(B−1)J, k0=eta+zeta, gamma0=rho+sigma, and

`Ctop=Q−F−Z−alpha−2d*x`.

The leading part of L is `L0=w*s²*k0*Q⁷`, of degree eleven. In the new
coordinates T has degree one, so the first factor has exact degree 22
and leading form `−L0²`. The remaining factor polynomials do not change.
The complete eight-factor degree lists are

```
normalized: 22,18,32,56,7,3,34,7  (sum 179)
ordinary:   22,18,32,24,7,3,22,7  (sum 135).
```

Their respective complete leading homogeneous forms are

```
−32 Q^108 h² gamma0 delta² i⁴ k0^13 w^18 s^30 Ctop,
+32 Q^80  h² gamma0 delta² i² f² k0^9 w^14 s^22 Ctop.
```

They are nonzero for every admissible fixed compiler slice. In particular
Q has nonzero coefficient B−1 and Ctop has coefficient −1 on F. The final
subtraction of one cannot affect them. Thus 179 and 135 are exact formal
degrees, not propagated upper bounds or degrees computed modulo constraints.
Three independent dense univariate coefficient expansions per source attain
the stated factor degrees and verify the displayed complete leading forms.

The new 86/179 point trades degree for one fewer operation. The 87/135
point improves the former 87/169 point at the same operation count. Existing
88/125 and lower-degree alternatives remain separate tradeoffs. This note
does not rerun the earlier 102,902 grouping choices or claim a globally
optimal circuit or operation/degree frontier.

## Reproduction and verification limits

The writer checks both symbolic coordinate identities, eighteen complete
factor/finalizer expression-DAG identities after the proved first-factor
cut, and both complete source ledgers and liveness. It evaluates 512 full
forward and 512 independently started inverse coordinate identities,
including signed and rational off-zero data. All 128 positive forward
maps remain positive. Six complete dense coefficient expansions verify
degree attainment and leading forms. The receipt also has exact Pell
components and bounded local ±1-unit cases supporting the inverse
positivity calculation; these are not full compiled-program witnesses.

The quantified positive-zero proof above, together with the exact full-source
identity and the authenticated parent's universality theorem, establishes
the universal result. No astronomical accepting Pell tower is materialized,
and finite fixtures are not substituted for the general theorem.

```sh
/tmp/diophantine-research-venv/bin/python complete86_factored_first_root.py \
  --root /path/to/native-stream-queue \
  --expect complete86_factored_first_root.json
```

Use Python with SymPy; the workspace path above is only an example interpreter.
`--output PATH` writes the deterministic receipt. Comparisons are recursive
and type-sensitive. Truncated, extended or wrong-coordinate parent sources
are rejected. The helper changes no historical source, receipt or repository
state. This is a conventional mathematical proof with executable audits,
not a Lean formalization or a literature-priority claim.
