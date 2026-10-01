# A full obstruction to the positive-transport 87-operation projection

Replacing the supplied positive packed field `F` by the computed positive
transport value `C` saves one addition in the actual
[coupled88 source](complete75_coupled_index_linear88.md). The resulting
**87 = 47M + 40A** polynomial is unsound: for every fixed complete75 compiler
and **every positive ordinary input**, it has a positive zero.

This is a full positive-witness construction, with both strict ratio slacks,
the full strong auxiliary norm, the input norm, and the remaining outer
constraints retained. The missing condition is precisely `F>0`. All zeros
constructed below restore a negative `F`, while all nineteen coordinates
actually supplied to the modified polynomial are strictly positive.
This rejects this exact projection. It makes no claim about other
87-operation candidates, including the distinct unresolved independent-gamma
construction, or about a general operation lower bound.

## 1. Exact source rewrite and fixed compiler scope

Fix any actual output of the complete75 compiler of
[the universal proof](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md), with the
mask exporter [new_constants](complete75_half_binomial_compiler.py).
In particular retain its fixed numerals

\[
 B=2^d,\quad d\ge4,\quad b>0\text{ odd},\quad
 K_0=DC+B\,DR>0,\quad 0<MC,MF<B-1.
\]

Here `MF` is the native exported mask: the source multiplies by
`MF+B-1`. All further compiler mask/layout hypotheses remain fixed. No
constant or program is chosen as a function of the ordinary input `x`.
The construction below works for every choice satisfying even these weaker
numerical conditions, so in particular for every actual compiled language,
including the empty language. It does not require a sampled mask to be a
valid compiler output.

The old source computes

\[
 q=(B-1)J+1,\quad C=q-F-Z-\alpha-2dx.
\]

Its four-subtraction chain is

    q_minus_F=q-F
    q_minus_FZ=q_minus_F-Z
    C_after_alpha=q_minus_FZ-alpha
    marked_rhs=C_after_alpha-2d*x.

Supply positive `Cpositive` instead of positive `F`, delete the last gate,
and reverse the other three:

    C_after_alpha=Cpositive+2d*x
    q_minus_FZ=C_after_alpha+alpha
    q_minus_F=q_minus_FZ+Z.

Alias every use of `marked_rhs` to `Cpositive`. The multiplication `2d*x`
was already paid and remains. No other factor definition, comparison,
product, or supplied coordinate is deleted. The resulting certificate has
86 operations and one comparison; subtracting one from the eight-factor
product gives 87 operations, with nineteen positive witnesses.

On arbitrary integer assignments it equals the old polynomial under the
exact substitution

\[
 F_{\rm old}=q-C- Z-\alpha-2dx.                    \tag{1}
\]

Every surviving old register has the same value. Thus there is a valid
forward map from every old positive zero: its recovered `C` is positive by
the parent theorem. The reverse map fails because (1) can be negative.

For reference, the outer registers of the modified source are exactly

\[
 \begin{aligned}
 W&=C-Z,&u&=2dx+b,\\
 R&=(q^2-Z-qF_{\rm old})(q^2-1)
       +(MC+q(MF+B-1))J,\\
 N_t&=(K_0+X)C+(q-F_{\rm old})-z_+(q-1).
 \end{aligned}                                                     \tag{2}
\]

The appearances of `F_old` in (2) are abbreviations for (1); the modified
DAG never computes it or tests its sign.

## 2. A fixed scale that makes the outer congruences compatible

Let `L=lcm(1,...,d)`. Multiply `L` by a power of two until its two-part is
at least 8, and write

\[
 t=D M,\quad D\text{ odd},\quad M=2^v\ge8.
\]

Then `d|t` and `D|2^t-1`. To prove the second claim, each odd prime power
`p^e` in `D` is at most `d`. Both `p^(e-1)` and `p-1` divide `L`; they
are coprime, so `phi(p^e)` divides `L`, hence `t`. Euler's theorem gives
the required congruence at every prime power. The case `D=1` is vacuous.

Fix, independently of `x`,

\[
 q=2^t,\qquad J=(q-1)/(B-1).
\]

Thus `q=0 mod M`, `q=1 mod D`, and

\[
 t\mid q(q^2-1).                                      \tag{3}
\]

Choose the unique representative `e` in `[0,4D)` satisfying

\[
 e\equiv (MC+MF+B-1)J\pmod D,\qquad e\equiv3\pmod4.
\]

Then `0<e<4D<t`. Choose `z0` in `[1,M]` with
`z0=e-MC J mod M`, and set `Z=q+z0`. In particular `Z>q`.
For the given positive input put

\[
 u=2dx+b,\quad W=2^u,\quad C=W+Z>q.                  \tag{4}
\]

Choose `alpha0` in `[1,q-1]` satisfying

\[
 \alpha_0\equiv1-(K_0+2^e)C-C-Z-2dx\pmod{q-1}.       \tag{5}
\]

For every `alpha=alpha0+(q-1)l`, formula (1) is strictly negative.
Modulo `D`, the first product in `R` vanishes and its mask is
`(MC+MF+B-1)J`. Modulo `M`, the first product is `Z` and the mask is
`MC J`. Therefore, **independently of alpha**,

\[
 R\equiv e\pmod t,\qquad R\equiv3\pmod4.             \tag{6}
\]

The first congruence uses both coprime parts of `t`; no assumption that
`d` is a power of two is made.

## 3. Enforcing the required population without a packed-width bound

Let `R0` be the index at `alpha0` and put

\[
 S=q(q^2-1)(q-1)>0.
\]

Increasing alpha by `(q-1)l` increases `R` by exactly `Sl`. This does not
change (6), by (3). Let

\[
 l_0=\lfloor R_0/S\rfloor+1,\qquad D_0=Sl_0-R_0,
 \quad 0<D_0\le S.
\]

For a sufficiently large integer `N`, choose `l=2^N-l0>0`. Then

\[
 R=S2^N-D_0=(S-1)2^N+(2^N-D_0).                    \tag{7}
\]

When `2^N>D0`, the two displayed blocks do not overlap and

\[
 \operatorname{pc}(R)=\operatorname{pc}(S-1)+N-
                       \operatorname{pc}(D_0-1).
\]

Consequently `N` can, and the source explicitly does, ensure

\[
 R>\max(3q+1,3t,u,e),\qquad
 R\equiv3\pmod4,\qquad \operatorname{pc}(R)\ge3t+2.  \tag{8}
\]

There is no upper bound `R<q^4`; its failure is part of the mechanism.
All of `q,J,C,Z,alpha` are positive. With `X=2^R`, equations (5)–(6)
give the exact positive integer

\[
 z_+=\frac{(K_0+2^R)C+(q-F_{\rm old})-1}{q-1}.       \tag{9}
\]

The numerator is positive, and replacing `2^R` by `2^e` changes it by a
multiple of `q-1`. Thus (9) gives `Nt=1`, with its essential final `-1`
in the numerator. This proves all needed outer identities, not merely
compatibility of an isolated index or mask.

## 4. Fresh half-binomial converse without the former upper bound

Only a **positive converse** beyond the old upper-bound domain is needed.
We do not extend the arbitrary-zero decoding theorem of
[half-binomial42](pell_kernel_half_binomial42.md).
For `q,R` in (8), let `r=(R-1)/2`, `X=2^R`, and define

\[
 M_R=\sum_{j=0}^{r}\binom{2r}{r+j}X^j,\qquad Y=M_R/2.
                                                               \tag{10}
\]

The numerator is even, and the exact central-binomial valuation gives

\[
 v_2(Y)=\operatorname{pc}(r)-1=\operatorname{pc}(R)-2\ge3t.
\]

Therefore `w=X/q^3` and `s=Y/q^3` are positive integers. Put

\[
 a=Y(X+1),\ E=XY,\ A=a+2,\ \Delta=A^2-1,\ H=4a+3,
 \quad P=2XY^2+1.
\]

Using the standard Pell sequences, set

\[
 c=\psi_A(R),\quad D_{\rm main}=\chi_A(R),\quad
 k=2\psi_P(r+1),\quad \tau=\chi_P(r+1).
\]

Both ratio slacks remain strictly positive. Here is the missing growth
check that permits the converse outside `R<q^4`. Define
`xi=(X+1)^(2r)/X^r`. Its binomial expansion and the chosen (10), before
assuming either ratio, give `xi=2Y+theta`, where `0<theta<1/4`; in
particular `xi<4Y`. Also `Y>=X^r/2`, so `4r/a<1/2` directly at these
chosen values. The elementary Pell bounds (11)–(12) in the parent §5
use only `6XY^2>a` and this growth condition. They yield

\[
 \xi<c/(k/2)<\xi(1+8r/a),\qquad
 0<c/k-\xi/2<4r\xi/a<16r/(X+1)<1/2.
\]

The last inequality holds for `R>=7`. This derivation does not import the
parent's ratio-dependent growth step (13) or assume its ratio conclusion.
Combining the error estimate with the already established binomial tail gives

\[
 Y<c/k<Y+1/8+1/2<Y+1.
\]

Thus `eta=c-kY>0` and `zeta=k-eta>0` are integers. No removed ratio is
being reintroduced as an assumption.

The parent converse's remaining definitions use no upper bound on `R`:

\[
 h=(k-R-1)/E>0,\qquad g=\tau-XY^2k>0.
\]

The first is integral because `P=1 mod E`; Pell growth makes it positive.
The second is positive by the first norm. Direct substitution gives
`N0=1` in its positive-root form and `Nk=k-R-hE=1`.

For a convenient proof of the main and input gamma integrality, set

\[
 G_j=\frac{\chi_A(j)-a\psi_A(j)-2^j}{H}.
\]

These are integers with `G0=G1=0`, `G2=1`, and

\[
 G_{j+2}=2A G_{j+1}-G_j+2^j.
\]

They are strictly increasing from `j=1`. Set `gamma=G_R>0`; then
`D_main=X+ac+gamma H`, and the main norm is exactly one.

Retain the full canonical minus auxiliary construction from the parent
§6 at these fresh parameters:

\[
 m=2cR,\quad f=\chi_A(m),\quad
 T=\Delta\psi_A(m),\quad i=T/c^2,\quad
 y=\psi_T(R),\quad V=\chi_T(R)/T,
 \quad o=(V+c)/f,\quad j=(V+R)/c.                    \tag{11}
\]

The canonical divisibility and minus-congruence identities depend on
`c=psi_A(R)` and `R=3 mod4`, not on a relation between `R` and `q^4`.
They make `i,o,j` positive integers. In particular `V>c>R`. They give

\[
 T^2=\Delta(f^2-1),\quad
 T^2(V^2-y^2)+y^2=1,\quad V=of-c=jc-R.
\]

Thus both the exact strong factor and the auxiliary factor are one, and
`Lnew=V-jc+k-hE=1`. The actual strong square is preserved.

## 5. Input extension and all nineteen positive coordinates

By (8), the positive odd index `u=2dx+b` satisfies `3<=u<R`. Define

\[
 \kappa=\psi_A(u),\quad\mu=\chi_A(u),\quad
 \delta=(\kappa-u)/\Delta,\quad
 \rho=G_u,\quad\sigma=G_R-G_u.
\]

For odd `u`, `psi_A(u)=u mod Delta`; strict Pell growth makes `delta>0`.
The recurrence above gives `rho,sigma>0`. Together with (4), these are
precisely the source's input definitions:

\[
 \kappa=u+\delta\Delta,\quad
 \mu=W+a\kappa+\rho H,\quad \rho+\sigma=\gamma,
 \qquad \mu^2-\Delta\kappa^2=1.
\]

We have now supplied all nineteen positive witnesses

    J,C,alpha,zplus,f,h,i,j,o,s,w,g,eta,zeta,y,Z,delta,rho,sigma.

Each of the eight actual source factors is exactly one: first norm, main
norm, input norm, auxiliary norm, index unit, transport unit, strong unit,
and coupled linear unit. Their product minus one vanishes. This works for
every positive `x` with the same fixed compiler numerals.

The complete modified projection is therefore the set of all positive
integers, regardless of the compiled language. For example, fixing any
actual compiler for the empty language gives false positives at every
input. The conclusion is stronger than a failed coordinate bijection or
a kernel-only example. Its constructive proof supplies the full enormous
witness tuple parametrically; it does not rely on finite masks being
interpreted as computation histories.

## 6. Executable checks and limits

The [checker](complete75_positive_transport_projection_obstruction.py)
and [receipt](complete75_positive_transport_projection_obstruction.json)
audit the exact gate deletion and 512 arbitrary-integer source identities;
93 period-scale constructions; 30 complete outer congruence/population
fixtures; eight fresh half-binomial main constructions with both ratios;
72 positive input splits; and five canonical full strong auxiliary tuples.
A materialized `q=2,R=31` main case lies beyond `R<q^4` and separately
checks the converse formulas. It is a small component check, not a full
compiler fixture. Likewise the finite outer mask fixtures supplement the
general construction without claiming that those masks encode histories.

The full compiler zeros proved above have astronomical Pell towers and
are not materialized by the default replay. Their existence follows from
Sections 2–5, with each retained factor verified algebraically.

```sh
/tmp/diophantine-research-venv/bin/python complete75_positive_transport_projection_obstruction.py
```

Independent root and native-controller proof/source reviews passed with no
remaining findings, and both reviewers ran the fresh default successfully.
They checked the exact source substitution, fixed period closure, both CRT
parts, population lift, positive transport quotient, noncircular
converse-only ratio argument, full canonical strong auxiliary extension,
and input recurrence. The all-actual-compiler theorem remains distinct
from the finite numerical mask and component fixtures.
