# A normalized strong auxiliary witness gives 87 operations

> Rejected shortcut: [multiplying the two quotient witnesses](complete75_multiplicative_gamma86_obstruction.md)
> produces a distinct86-operation source with no positive zeros on any valid
> compiler slice. The established87 theorem below is unchanged; this does not
> settle the independent-gamma87 route or all possible86-operation sources.

The complete fixed compiler now gives a universal Diophantine polynomial
with **87 operations = 48 multiplications + 39 additions/subtractions**,
**19 strictly positive existential witnesses**, and exact total degree
**203**. This improves the operation count of
[coupled88](complete75_coupled_index_linear88.md) by one. The old
88-operation degree151 polynomial remains a useful degree tradeoff, and
the separate 75-operation comparison certificate is unchanged.

The new polynomial has exactly the same positive ordinary-input projection
as coupled88 under its full fixed compiler hypotheses. Soundness is an
explicit positive embedding into the old source. Completeness rebuilds
five canonical auxiliary witnesses. It does **not** assert a bijection of
all old and new positive tuples, or equality of the two polynomials on
arbitrary assignments.

Both strict ratio slacks, positive packed fields, the ordinary-input
width and norm, and the complete strong auxiliary condition remain proved.
No compiler constant, mask or input convention is weakened.

## 1. Definitions and the one changed witness

Keep precisely the fixed constants and compiler contract in
[coupled88 §1](complete75_coupled_index_linear88.md). In particular the
ordinary input is still `x>0`, and all masks are the actual compiler masks,
with `B=2^d`, `d>=4`, and the same population and congruence conditions.
Keep the nineteen positive coordinate names

    J,F,alpha,zplus,f,h,i,j,o,s,w,g,eta,zeta,y,Z,delta,rho,sigma.

The source calls `J,g,y` respectively `Jrep,tau_gap,y_aux`. Only the
meaning of `i` changes. All the following main and outer definitions are
identical to the parent:

\[
 \begin{aligned}
 q&=(B-1)J+1,&X&=wq^3,&Y&=sq^3,&E&=XY,\\
 k&=\eta+\zeta,&c&=kY+\eta,&a&=E+Y,\\
 A&=a+2,&\Delta&=A^2-1,&H&=4a+3,\\
 D&=X+ac+(\rho+\sigma)H,&V&=of-c.
 \end{aligned}
\]

The packed index `R`, transport factor, input norm and coupled linear
factor remain literal parent expressions. In particular neither `F>0`
nor either ratio coordinate is removed.

Supply the new positive `i` and compute

\[
 t=ic^2,\qquad Q=\Delta t^2,\qquad K_*=\Delta Q=\Delta^2t^2.
                                                               \tag{1}
\]

Replace just the auxiliary and strong factors by

\[
 N_3^*=K_*(V^2-y^2)+y^2,\qquad N_4^*=f^2-Q.          \tag{2}
\]

The other six parent factors are unchanged. The polynomial is

\[
 P_{87}=N_0N_1N_2N_3^*N_kN_tN_4^*L-1.              \tag{3}
\]

The mathematical quantity `T=Delta*t` will occur in the proof; evaluating
it is not an uncharged instruction. The literal circuit evaluates `K_*`
by the two displayed products defining `Q` and `Delta*Q`, and uses `Q`
again in the strong factor.

## 2. Positive soundness without a new index or sign argument

For every integer `a`,

\[
 \Delta=(a+2)^2-1\equiv0\text{ or }3\pmod4.
\]

Therefore `f^2-Delta*t^2` cannot be `-1`: if `Delta=0 mod4` it is a
square modulo4; if `Delta=3 mod4` it is a sum of two squares modulo4.
This obstruction is unconditional and requires no typing or other source
equation.

At an integer zero of (3), every factor is an integer unit. Consequently

\[
 N_4^*=1,\qquad f^2-1=\Delta t^2.                  \tag{4}
\]

Map to the parent coordinates by

\[
 i_{\rm old}=\Delta i,                              \tag{5}
\]

leaving every other supplied coordinate unchanged. This preserves strict
positivity before using any equation: all positive source coordinates
give `a>0`, hence `Delta>0`.

The parent's strong parameter is now `T_old=i_old*c^2=Delta*t`. Its
coefficient and strong unit are

\[
 \begin{aligned}
 K_{\rm old}&=\Delta(f^2-1)=\Delta^2t^2=K_*,\\
 N_{4,\rm old}&=1+T_{\rm old}^2-K_{\rm old}
              =1+\Delta(1-N_4^*)=1.
 \end{aligned}                                                     \tag{6}
\]

Thus the parent auxiliary factor equals `N3*`, its strong factor equals
`N4*`, and all six other factors agree identically. Its whole product is
one. We have produced a genuine positive zero of the complete old88
polynomial. Its established compiler theorem then gives precisely the
same accepted ordinary input.

This argument restores the **full strong square**, not just a weaker
Pell relation. It needs no new proof about possible signs of the index,
transport or linear factors, and assumes none of their conclusions
before the embedding. All parent positivity, mask and ordinary-input
requirements apply to the restored tuple.

## 3. Canonical completeness and the additional divisibility

Conversely take any positive parent zero. The proved parent theorem gives

\[
 c=\psi_A(R),\quad R\equiv3\pmod4,
 \quad k=R+1+hE,
\]

and all its eight factors equal one. Retain every coordinate except
`f,i,j,o,y`. Reconstruct those five at the same main `A,c,R`.

Let

\[
 m=2cR,\quad f=\chi_A(m),\quad
 i=\psi_A(m)/c^2,\quad T=\Delta\psi_A(m).            \tag{7}
\]

The new division is integral. Write `C=chi_A(R)` and expand

\[
 (C+c\sqrt\Delta)^{2c}.
\]

Its coefficient of `sqrt(Delta)` is `psi_A(2cR)`. The term with one
square-root factor is `2c^2 C^(2c-1)`, divisible by `c^2`. Every remaining
odd term contains `c^j` for `j>=3`, hence is divisible by `c^2` as well.
All terms are integers, so `c^2 | psi_A(m)`. Equivalently, Pell composition
writes `psi_A(m)=c psi_C(2c)`, whose second factor is divisible by `c`.
Strict Pell positivity gives `i>0`.

Use the same full canonical minus construction as
[half-binomial42 §6](pell_kernel_half_binomial42.md):

\[
 y=\psi_T(R),\quad V=\chi_T(R)/T,\quad
 o=(V+c)/f,\quad j=(V+R)/c.                         \tag{8}
\]

Those canonical identities, at `m=2cR` and `R=3 mod4`, give integral
positive `y,o,j` and

\[
 \begin{aligned}
 T^2&=\Delta(f^2-1),\\
 T^2(V^2-y^2)+y^2&=1,\\
 V&=of-c=jc-R.
 \end{aligned}                                                     \tag{9}
\]

These are exactly the parent's canonical auxiliary witnesses; the only
extra fact established here is that its canonical
`i_old=Delta*psi_A(m)/c^2` is divisible by `Delta`.

With (7), the new `t=ic^2` equals `psi_A(m)`. The ordinary Pell identity
gives `N4*=f^2-Delta*t^2=1`; (9) gives `N3*=1`. Finally

\[
 L=V-jc+k-hE=-R+(R+1)=1.
\]

All other factors are unchanged and remain one. This yields a positive
zero of (3). The construction keeps the same ordinary input, fixed
compiler constants, main/input Pell data, both ratio slacks and outer
packed fields. It changes only the five listed auxiliary coordinates.

Consequently the projections agree even after retaining the other
fourteen supplied coordinates. An arbitrary old tuple need not have an
integral `i_old/Delta`; the proof uses fresh canonical auxiliaries instead
of making that unsupported assertion.

## 4. Literal arithmetic saving

The old seven-gate block was

    f2=f*f                      M
    f2minus1=f2-1               A
    K=Delta*f2minus1            M
    T=i_old*c2                  M
    T2=T*T                      M
    strong_difference=T2-K     A
    N4=strong_difference+1      A

It cost `4M+3A`. The replacement is

    t=i*c2                      M
    t2=t*t                      M
    Q=Delta*t2                  M
    Kstar=Delta*Q               M
    f2=f*f                      M
    N4star=f2-Q                 A

It costs `5M+1A`, exactly one operation less. The already paid `c2=c*c`
is shared in both schedules. The auxiliary factor still uses one product
of its coefficient by `V^2-y^2`, plus `y^2`; its gate count is unchanged.

The actual [source](complete75_normalized_strong87.py) deletes only
`f_square_minus_one`. It changes just `R16`, `strong_difference` and
`norm_strong`; all83 other retained instructions are literal parent rows.
For audit stability their historical names are retained:

| Register | New value |
|---|---|
|`ic2`|`t=i*c^2`|
|`ic22`|`t^2`|
|`strong_difference`|`Q=Delta*t^2`|
|`R16`|`Kstar=Delta^2*t^2`|
|`norm_strong`|`f^2-Q`|

The source register `A` denotes the discriminant `Delta`, as in the parent;
it does not denote the proof's Pell parameter `A=a+2`.

The complete certificate has **86=48M+38A**, one comparison, and19
positive witnesses. Its single final subtraction gives the claimed
**87=48M+39A** polynomial. No free division, square root, magnitude test,
canonicalization cost, or additional equation is used by the circuit.
Canonical witnesses are supplied existentially, exactly as in the parent
positive converse.

## 5. Exact degree and evidence

With all free input/witness coordinates of degree one, the factor degrees
in the product's order are

    14,22,42,64,9,5,38,9.

Only the auxiliary and strong factors change degree. Put
`Q0=(B-1)J`, `k=eta+zeta`, and

\[
 C_{\rm top}=Q_0-F-Z-\alpha-2dx.
\]

The highest homogeneous term is

\[
 32Q_0^{135}h^2(\rho+\sigma)\delta^2 i^4 k^{12}
     w^{17}s^{28}C_{\rm top}(2g-k).                  \tag{10}
\]

It is a nonzero polynomial of degree203. More explicitly, if
`Delta_top` and `c_top` denote the unchanged leading forms, the new strong
factor has leading form `-Delta_top*i^2*c_top^4`, while the new auxiliary
factor has leading form `Delta_top^2*i^2*c_top^6`. Their product changes
the old leading sign and removes `f` from the highest form. The parent
main/input norm cancellation identities supply the unchanged degrees22
and42; the final subtraction of one cannot affect (10).

The [receipt](complete75_normalized_strong87.json) verifies the literal
ledger and512 complete factor/polynomial identities, including128 signed
assignments and deliberately negative computed input roots. For arbitrary
assignments under (5), it checks the exact corrections

\[
 \begin{aligned}
 N_{4,\rm old}&=1+\Delta(1-N_4^*),\\
 N_3^*&=N_{3,\rm old}+\Delta(1-N_4^*)(V^2-y^2).
 \end{aligned}
\]

It also checks all64 residue cases for the unconditional negative-unit
obstruction, ten materialized full canonical auxiliary families,66
canonical composition residue cases, and three independent weighted and
offset univariate evaluations attaining degree203 and the precise leading
form (10). These finite auxiliary examples verify the canonical identities;
they are not claimed to materialize a complete accepting compiler tuple.
The universal positive-extension statement is proved in Sections2–3.

```sh
/tmp/diophantine-research-venv/bin/python complete75_normalized_strong87.py
```

Independent root, native-controller and substrate proof/source reviews
passed with no findings, and all three reviewers ran the fresh default
successfully. They checked the unconditional sign argument, restoration of
the complete old strong condition, the five-coordinate canonical converse,
all literal gate counts and the exact degree/leading form. Native-controller
also passed320 independently evaluated full eight-factor polynomial cases
(160 signed) and272 modular matrix checks of the canonical divisibility.
Root independently derived all eight factor degrees and (10).
