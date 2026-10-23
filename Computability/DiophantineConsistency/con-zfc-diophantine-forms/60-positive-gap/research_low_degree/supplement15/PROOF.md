# The degree-24 transport refinement

## 1. Statement, domain, and fixed instance

Let `Z_{>0}` denote the strictly positive integers. Fix the four concrete
integer ports specified by `native/COEFFICIENT_BINDING.json`, with aliases

```text
beta -> beta,  K0 -> K,  MC -> MC,  MF -> MF_source.
```

This is the complete compact source-44 coefficient tuple. In particular,
`beta = 2^590069 - 1`; `MF_source` is the shifted source port. Every port is
materialized as an unsigned little-endian integer in the four included gzip
payloads. The deterministic source-44 builder reconstructs the same tuple
from the included 430 literal K215 transitions; its independent auditor
reconstructs it from the pinned 943-tile list. The current retrieval snapshot
is ProveIt commit `beb0192cb8dc36f78c369c080f2adfbc1887a486`. The internal
historical source pins in inherited documents remain unchanged.

**Theorem (local arithmetic result).** The polynomial `P_new` defined below
has fifteen strictly positive unknowns, exact total degree 24, and an
89-operation evaluator. Its positive zero set is in affine bijection with
the positive zero set of the source-58 parent `P58`. In particular,

\[
 \exists\mathbf x\in\mathbb Z_{>0}^{15}\;P_{\rm new}(\mathbf x)=0
 \quad\Longleftrightarrow\quad
 \exists\mathbf x\in\mathbb Z_{>0}^{15}\;P_{58}(\mathbf x)=0.
\]

This local arithmetic statement is unconditional: it assumes neither the
consistency nor the inconsistency of ZFC.

**Conditional consistency corollary.** If the inherited source calibration
and arithmetic/compiler correctness are internalized for the chosen ZFC
syntax, yielding an internal proof that source-58 unsolvability is
equivalent to the corresponding syntactic consistency sentence, then the
same internal equivalence follows for `P_new` by the local reduction.
This supplement does not supply that internalization. The pinned
repository's `upstream/OBJECT_ZFC.md` explicitly leaves both the internal
source calibration and the arithmetic/compiler correctness bridge open.
An external equivalence over the standard natural numbers is not an
internal ZFC proof and does not alone imply correctness for the internal
natural numbers of every ZFC model.

The precise new result is a one-operation refinement of the pinned
source-58 degree-24, fifteen-positive construction. It does not reduce the
variable count, degree, or fixed coefficient heights.

## 2. Explicit equation

The fifteen supplied unknowns, all strictly positive, are

\[
 j,F,\alpha,z,f,h,i,T,X,Y,r,\eta,\zeta,u,\gamma.
\]

Define the following abbreviations; they introduce no further unknowns:

\[
\begin{aligned}
 J&=3j+1,&q&=\beta J+1,&C&=q-F-\alpha,\\
 E&=XY,& k&=\eta+\zeta,&c&=kY+\eta,\\
 a&=E+Y,&H&=4a+3,&\Delta&=a^2+H,\\
 D_0&=X+ac+\gamma H,&\ell&=EkY,&I&=ic^2,\\
 G&=(q-1)(q-F)+\alpha,&&&
\end{aligned}
\]

\[
\begin{aligned}
 R&=G(q^2-1)+(M_C+qM_F)J,\\
 \widehat R&=k-hE-1,\\
 U&=\Delta(f^2-1),\\
 V&=f^2(cT-\widehat R)-c.
\end{aligned}
\]

The six residuals are

\[
\begin{aligned}
 A_0&=[q^3(\ell+r)+Y]^2-q^6[\ell(\ell+k)+1],\\
 A_1&=(qD_0+XH)^2-q^2(\Delta c^2+1),\\
 A_k&=\widehat R-R,\\
 A_t&=C(qK_0+X)-q[F+z(q-1)],\\
 A_a&=(V+u)^2-Uu(2V+u)-1,\\
 A_s&=I^2-U.
\end{aligned}
\]

Set

\[
 P_{\rm new}=A_0^2+A_1^2+A_k^2+A_t^2+A_a^2+A_s^2.
\]

Every expression is a polynomial over the integers. All displayed powers
have fixed exponents. The abbreviation names specify a division-free
arithmetic circuit, not existentially quantified registers.

## 3. The exact transport identity

The positive transport shift is already used in the inherited ordinary
kernel. The new observation here is its one-gate saving when applied to the
literal source-58 integral-root evaluator.

Write `z_old` for source 58's positive transport coordinate and retain the
same names for all other coordinates. Its transport residual is

\[
 A_t^{\rm old}
  =q[K_0C+(q-F)-z_{\rm old}(q-1)]+XC-q.
\]

Substitute `z_old = z + 1`. In the free ring
`Z[q,K0,C,F,X,z]`, without imposing any residual equation,

\[
\begin{aligned}
 A_t^{\rm old}\big|_{z_{\rm old}=z+1}
 &=q[K_0C+(q-F)-(z+1)(q-1)]+XC-q\\
 &=qK_0C-qF-qz(q-1)+XC\\
 &=C(qK_0+X)-q[F+z(q-1)]\\
 &=A_t.
\end{aligned}
\]

The other five residuals contain no transport coordinate and are unchanged.
Consequently the exact whole-polynomial identity is

\[
 P_{\rm new}(j,F,\alpha,z,\ldots)
 =P_{58}(j,F,\alpha,z+1,\ldots).
\]

The checker proves this identity locally by exact free-ring expansion,
checks the actual transport subgraphs against that expansion, and checks
that the other five residual subgraphs agree with the imported original
source-58 circuit. It does not infer identity from sampled evaluations.

## 4. Positivity of the inverse substitution

The forward map from a positive zero of `P_new` to a positive zero of `P58`
is immediate: keep all coordinates except `z_old = z + 1 > 0` and apply the
identity above. The converse requires proof that every positive source-58
zero has `z_old >= 2`.

The source-58 soundness reconstruction first forces `q^3 | Y` and `q | X`
from its two integral-root residuals. It therefore recovers positive
integers

\[
 s=Y/q^3,\qquad w=X/q
\]

and a positive ordinary-kernel tuple. The ordinary kernel supplies

\[
 C>0,\qquad X=2^R,\qquad w>q>F.
\]

These statements are proved before the transport shift in Sections 3,
6, and 7 of `upstream/ORDINARY_KERNEL.md`; source 58's soundness proof
recovers exactly its positive-kernel hypotheses. In particular, `w > q`
does not follow from divisibility alone: it uses the inherited index and
power-of-two recovery.

Divide the vanishing old transport residual by the already known positive
integer `q`, and use `X = qw`. This gives

\[
 (K_0+w)C+(q-F)-z_{\rm old}(q-1)=1,
\]

or equivalently

\[
 (z_{\rm old}-1)(q-1)=(K_0+w)C-F.
\]

The right side is strictly positive because `C >= 1`, `K0 > 0`, and
`w > F`. Also `q > 1`. Hence `z_old - 1 > 0`. Since the coordinates are
integers, `z_old >= 2`, so `z = z_old - 1` is a strictly positive integer.

The two affine maps are inverse on the positive zero sets. We have proved
the stronger conclusion of a bijection between those zero sets, and in
particular

\[
 \exists\mathbf x>0\;P_{\rm new}(\mathbf x)=0
 \quad\Longleftrightarrow\quad
 \exists\mathbf x>0\;P_{58}(\mathbf x)=0.
\]

This proves the stated unconditional local arithmetic theorem. It also
preserves any internally established consistency calibration of the parent
equation. The further consistency corollary in Section 1 remains
conditional on the inherited internalization obligations; composing with
an external source equivalence does not discharge them.

## 5. Exact total degree

Give each of the fifteen supplied unknowns degree one and each fixed port
degree zero. The raw circuit has degree cancellations. Put
`Z = X + gamma H`, so `D0 = ac + Z`. The exact identities

\[
\begin{aligned}
 A_0={}&q^6\{r^2+\ell(2r-k)-1\}
          +2q^3(\ell+r)Y+Y^2,\\
 A_1={}&q^2\{2acZ+Z^2-Hc^2-1\}
          +2qD_0XH+(XH)^2
\end{aligned}
\]

give residual degree upper bounds

\[
 (\deg A_0,\deg A_1,\deg A_k,\deg A_t,
       \deg A_a,\deg A_s)\le(11,9,4,3,12,10).
\]

The degree-12 homogeneous part of `Aa` is

\[
 -2X^2Y^3f^4u\{(\eta+\zeta)T+hX\}.
\]

Thus only `Aa^2` contributes in degree 24, and

\[
 \operatorname{in}_{24}(P_{\rm new})
   =4X^4Y^6f^8u^2\{(\eta+\zeta)T+hX\}^2.
\]

The coefficient of `X^6 Y^6 f^8 u^2 h^2` is exactly 4, independently of
all four fixed ports. Therefore the degree is exactly 24 for the concrete
included tuple, not merely for generic coefficient values. The exact
auditor verifies both cancellation identities, their actual circuit
instances, and this leading form in an integer polynomial ring with the
coefficient ports retained as formal symbols of weight zero.

The cancellation-expanded evaluator has 101 gates. It is a degree
certificate and is not substituted for the counted 89-gate evaluator.

## 6. Operation count

The counted metric is the number of live binary `+`, `-`, and `*` gates
after common-subexpression sharing. Multiplication by any fixed numeral
is charged; fixed leaves and references to earlier gates are free. There
are no division, exponentiation, or equality-test gates.

With `q`, `q-1`, `q-F`, `C`, and `X` already available, the old transport
residual uses eight gates. The revised residual uses seven:

```text
t1 = q * K0
t2 = t1 + X
t3 = C * t2
t4 = z * (q-1)
t5 = F + t4
t6 = q * t5
At = t3 - t6
```

The complete shared residual evaluator has 78 gates instead of 79. Six
squarings and five additions form the sum of squares, producing **89
instead of 90**. The final breakdown is 47 multiplications, 27 additions,
and 15 subtractions. `build.py` deterministically materializes the circuit;
`verify.py` independently verifies topology, liveness, input list, and
counts from the JSON packet. No minimality claim is made.

## 7. The all-one tuple

Set all fifteen supplied unknowns to one, leaving the four authentic fixed
ports untouched. Then `k=2`, `c=3`, `a=2`, `Delta=15`, `f=1`, `U=0`, and
`I=9`. Consequently

\[
 A_s=I^2-U=81,\qquad P_{\rm new}(1,\ldots,1)\ge81^2=6561.
\]

The all-one tuple is not a solution. This obstruction is independent of
all fixed coefficient ports; the verifier checks that the strong residual
has no coefficient-port ancestor. No positive zero is exhibited or assumed.

## 8. Proof dependencies and reproducible evidence

The local affine reduction needs only the exact transport identity and the
positive-zero bounds in Section 4. The inherited ordinary semantic chain,
whose internalization is a separate obligation, is:

1. The external calibrated K215 endpoint identifies blank halting with
   a finite refutation in the fixed effective ZFC proof calculus. The
   internal version of this source calibration is not supplied here.
2. The complete compact source-44 native tuple and its controller give the
   intended computation encoding in the inherited ordinary argument. See
   `native/PROOF.md`, with the literal tuple and transition data in that
   directory. Its correctness for every model's internal natural numbers,
   or corresponding object-language derivations, is not supplied here.
3. The inherited ordinary Pell kernel gives the arithmetic encoding and
   the bounds `C>0`, `X=2^R`, `w>q>F`. See
   `upstream/ORDINARY_KERNEL.md` and `upstream/PELL_LEMMAS.md`.
4. Source 58's report, Sections 4--6, proves the two integral-root scale
   recoveries and the canonical positive-gap converse for its degree-24
   polynomial. The whole compact44 tuple supplies the canonical odd rank
   and the congruence `R = 3 mod 4` used there.
5. Sections 3--4 above give the new affine bijection of positive zero sets.

The included `upstream/RELAXED_KERNEL_COMPLETE.md` is an additional inherited
ordinary reference. Any historical coefficient instances in that text are
not substitutions for this supplement's complete compact44 binding.

`PROVENANCE.json` identifies the source snapshot and imported-file digests.
The inherited native `SOURCE_PINS.json` records twelve historical source
files with Git blob identities; its auditor checks them all. The native
auditor also independently reconstructs the four literal integers, checks
66062 finite basis identities and the actual rank controller, and verifies
the authentic 430-transition machine binding. Its finite computations
support the supplied universal native proof rather than replace it.

The local exact audit checks both ordinary and optimized Python execution;
its validation uses explicit exceptions, so `python3 -O` cannot disable
the checks. Sample evaluations are labeled as transcription evidence.

The current pinned object-language status is preserved unmodified in
`upstream/OBJECT_ZFC.md`. Its remaining route requires both an internal
source/refutation calibration and arithmetic representation/compiler
correctness for every model's internal natural numbers, followed by the
appropriate completeness argument or explicit object-language derivations.
Neither standard-natural truth nor agreement on external numerals handles
all nonstandard witnesses. The stronger internal claims in historical
parent prose are therefore not used as a completed internal endpoint.

This supplement supplies the local positive-zero bijection and exact
independently checked algebra. Its internal `Con(ZFC)` corollary remains
conditional on the stated inherited internalization, and it supplies no
new end-to-end Lean/Rocq certificate or object-language ZFC equivalence
derivation. It proves no consistency statement and makes no claim that the
resulting equation is globally simplest.

