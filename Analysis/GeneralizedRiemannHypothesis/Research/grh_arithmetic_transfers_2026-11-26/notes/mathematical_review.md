# Independent critical review of the exact congruence-depth refinement

Reviewed: `research/candidate_notes.md`, the parent agent's finite trace-certificate proposal,
and the parent agent's bad-prime example. Upstream source inspected at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.

## Verdict

The central exact-length theorem is correct with the stated integral matrix-span assumptions.
Its identification with the upstream conjugate-dual module is correct, including the inverse,
transpose, and cyclotomic factor. It therefore removes the rank factor from the *global*
scalar-discrepancy bound in `SelmerData.lean`, and consequently from the isolated global term
in `MainSummands.lean`. This does not remove rank factors from the local terms.

The parent's finite word-trace certificate is correct, with maximum word length
`2d^2-1`. The bad-prime counterexample and its exact module-length formula are also correct.
The principal qualifications are the integral, rather than merely rational, span assumption;
the noncanonical identification of finite character modules; normalization by ramification
index; and the need for generation of the group or its joint representation image.

No central mathematical error was found. The result should continue to be presented as a
classical representation-theoretic sharpening of an upstream estimate, not a newly resolved
open conjecture.

## 1. Exact finite-level length

Let `O` be a DVR, `pi` its uniformizer, and let `rho,sigma:G -> GL_d(O)` with `d>0`
have O-linear matrix span `M_d(O)`. Set

\[
a=\min_{g\in G}v_\pi(\operatorname{tr}\rho(g)-\operatorname{tr}\sigma(g)),
\quad
H_n=\operatorname{Hom}_{(O/\pi^n)[G]}(\rho_n,\sigma_n).
\]

The convention is `v_pi(0)=infinity`; if all discrepancies vanish, `a=infinity`.
If at least one is nonzero, well-ordering of the nonnegative integers ensures that the
minimum is attained. No finiteness of `G` is needed.

### Trace rigidity

The trace pairing on `M_d(A)` is perfect for every commutative ring `A`, because the
matrix units `E_ij` pair with `E_ji`. Thus there is no requirement that `d` be a unit,
and no division by `d` occurs. The candidate's proof that equal traces modulo `pi^r`
give an algebra isomorphism between the two full matrix algebras is valid. The innerness
argument over the local ring `O/pi^r` is also valid. In particular, the theorem does not
fail when the residue characteristic divides the dimension.

### Cyclicity

The submodule of `H_n` killed by `pi` is exactly

\[
\pi^{n-1}\operatorname{Hom}_{k[G]}(\overline\rho,\overline\sigma).
\]

To be precise, multiplication by `pi^{n-1}` identifies the right-hand residual matrix
space with the pi-torsion matrices modulo `pi^n`; the equivariance equations agree.
The residual Hom space is zero or one-dimensional, by absolute irreducibility and the
fact that the centralizer of the full matrix algebra is `k`. Finite-length DVR module
structure therefore implies that `H_n` is zero or cyclic.

If a generator of a nonzero `H_n` has order `pi^r`, it has the form
`pi^{n-r}Y` with `Y` primitive modulo `pi^r`. The residual `Y` is a nonzero map between
irreducible representations of the same dimension, hence an isomorphism. Therefore
`Y` is invertible modulo `pi^r`. This proves `r<=a`. Conversely an invertible intertwiner
modulo `pi^s`, `s=min(n,a)`, gives an element of exact order `pi^s` in `H_n`.

Hence, noncanonically,

\[
H_n\simeq O/\pi^{\min(n,a)},\qquad
\operatorname{length}_O H_n=\min(n,a).
\]

The isomorphism is not claimed to select compatible generators as `n` varies. The length
formula and the supremum do not need such a choice.

## 2. Exact match with the upstream dual

`grh/src/New/Congruences/Selmer/SelmerData.lean:59-77` defines `conjDualHom` by

\[
\eta(\rho(g)u)(m)
 =\eta(u)\bigl(\chi(g^c)\rho(g^c)^{-1}m\bigr).
\]

Here `c` conjugates the group element. It does **not** conjugate coefficients of `O`.
Choose a generating additive character `lambda` of `O/pi^n`, so that the O-linear
identification of its character module with `O/pi^n` is given by
`b -> [x -> lambda(bx)]`. With the convention

\[
\eta(u)(m)=\lambda(m^T X u),
\]

the defining relation becomes

\[
X\rho(g)=\chi(g^c)\rho(g^c)^{-T}X.
\]

Thus the target representation is exactly

\[
\sigma(g)=\chi(g^c)\rho(g^c)^{-T}.
\]

The character-module identification exists because upstream `O` is a finite extension's
p-adic integer ring, so `O/pi^n` is a finite local principal ring. One elementary proof
is to choose an additive character nonzero on its socle: its O-annihilator is zero,
and equality of cardinalities makes it an O-module generator. The identification is
noncanonical but module lengths are invariant. Do not claim such a finite-character
identification for every abstract DVR with an infinite residue field.

The target's full integral matrix span follows from that of the source: `g -> g^c`
and inversion permute group elements, transpose is an O-linear bijection, and the
cyclotomic factors are units. Multiplying each member of a spanning family by its own
unit does not change its O-linear span.

Every nonzero `b in O` is associated to `pi^n`. Therefore the source's supremum over
all `b!=0` of finite character-module Hom lengths equals the above supremum over `n`.
The value of `congruenceTerm` is exactly `a`.

### Scalar witness and normalization

The source's scalar witness is

\[
\rho(g)=\alpha I,\qquad
\rho((g^c)^{-1})=\alpha'I,\qquad
\Delta=\alpha-\chi(g^c)\alpha'.
\]

This scalar annihilates every finite-level Hom module. Since these modules are cyclic,
their lengths are at most `v_pi(Delta)`, giving the strengthened global bound.
This uses the actual matrix scalar gap, not its trace `d Delta`; dividing the scalar
trace by `d` would be invalid at primes dividing `d`.

`MainSummands.lean:145-179` already bounds the normalized valuation of this exact gap
by `padicValNat ell D.chosenGroupOrder`. Replacing its call to the old global bound
therefore removes precisely its leading `card n` factor. Its calculation uses the
natural-number expression `t-1+1`; for `t=0` this is 1, not 0. The candidate preserves
that source proof rather than incorrectly rewriting the exponent as `t` in every case.

If `e=v_pi(ell)`, raw O-module length is `a`, while the source's normalized length is
`a/e`. State which valuation convention is used in every numerical application.

## 3. Finite trace certificate: complete proof

Suppose a finite set `S` generates `G`, set `m=d^2`, and the matrices of `rho(G)` span
`M_d(O)`. There exist group words `g_1=1,g_2,...,g_m` of length at most `m-1`
whose matrices `R_i=rho(g_i)` are an O-basis.

**Existence of short basis words.** Reduce modulo `pi` and let `W_j` be the span of
positive words of length at most `j` in the chosen generators. It starts with dimension
one. If `W_j=W_{j+1}`, then it is invariant under left multiplication by each generator.
These multiplications are invertible linear maps, so their inverses preserve `W_j` too.
The span of the whole group image would then be `W_j`. Consequently the dimensions
increase at every stage before reaching `m`; they reach `m` by stage `m-1`. Extend
the identity to a basis from these group words and lift the basis to O. Its determinant
is a unit, so it is an O-basis, not merely a fraction-field basis. Symmetry of `S` is
unnecessary for this positive-word construction.

For `A=O/pi^r`, write `S_i=sigma(g_i)`. Test the finite set of trace congruences

\[
\operatorname{tr}\rho(g_i g_j)=\operatorname{tr}\sigma(g_i g_j),
\qquad
\operatorname{tr}\rho(s g_i g_j)=\operatorname{tr}\sigma(s g_i g_j)
\quad(s\in S)
\]

in A. The first set says that the trace Gram matrices of `R_i` and `S_i` coincide.
The former has unit determinant, so the latter does too. Thus `S_i` also form an A-basis.
Let `Phi:M_d(A)->M_d(A)` be the A-linear map `R_i -> S_i`. It is invertible,
preserves the trace pairing, and sends the identity to the identity because `g_1=1`.

For every generator `s`, and every `i,j`, the second set gives

\[
\operatorname{tr}\bigl(\Phi(\rho(s)R_i)S_j\bigr)
 =\operatorname{tr}\bigl(\sigma(s)S_iS_j\bigr).
\]

Perfectness of the trace pairing implies
`Phi(rho(s)R_i)=sigma(s)S_i`. By linearity this holds for arbitrary right factors.
It extends to inverse generators and then every `g in G`. Taking the right factor to
be the identity gives `Phi(rho(g))=sigma(g)`. Taking arbitrary linear combinations
of the basis matrices as left factors shows that `Phi` is an algebra automorphism.
It is inner over the local ring A, proving equivalence of the representations modulo
`pi^r`. Conversely equivalence implies all the tested congruences.

Therefore the minimum valuation among this finite set of trace discrepancies equals the
minimum over all group elements. Pair words have length at most `2m-2`, and the words
with one additional generator have length at most `2m-1=2d^2-1`. There are at most
`(|S|+1)m^2` tests before duplicate words are removed.

### Essential generation caution

It is not enough for `S` to generate `rho(G)` alone. It must generate G, or, in the
continuous setting, topologically generate the **joint image** of `(rho,sigma)`.
Otherwise the kernel of rho can contain an element on which sigma is nontrivial;
the free-group example's `z` does exactly this. A finite list of Frobenius elements
without a generation certificate supplies upper bounds on `a`, not an exact value.

For continuous representations, the proof extends to topological generation because the
intertwining equations are closed and equality on a dense subgroup extends to its closure.
This qualification should be explicit if the finite test is proposed for absolute Galois
representations, whose group is not being presented by a given finite generating set.

## 4. Bad-prime counterexample

Let p be odd and `a,c>=1`. On the free group generated by `u,v,z`, take

\[
\rho(u)=\sigma(u)=I+p^cE_{12},\quad
\rho(v)=\sigma(v)=I+p^cE_{21},\quad
\rho(z)=I,\quad \sigma(z)=(1+p^a)I.
\]

The fraction-field image algebra is all `M_2(Q_p)`, because differences of the two
unipotents from the identity recover `E_12,E_21` after division by `p^c`, and their
products recover the diagonal units. But the integral image is scalar modulo p;
it does not span `M_2(Z_p)`.

For `X=[[t,y],[z,t+h]]` modulo `p^n`, the u and v equations say

\[
p^c y=p^c z=p^c h=0,
\]

while the z equation says `p^a X=0`. In these coordinates this is equivalent to

\[
p^a t=0,\quad
p^{\min(a,c)}y=p^{\min(a,c)}z=p^{\min(a,c)}h=0.
\]

The coordinate change from `(x,y,z,w)` to `(t,y,z,h)=(x,y,z,w-x)` is unimodular;
there is no division by two in the module computation. Hence

\[
\operatorname{length}H_n
 =\min(n,a)+3\min(n,a,c).
\]

The trace-depth assertion uses that p is odd: for every word g,
`sigma(g)=(1+p^a)^{e_z(g)}rho(g)`, so all trace discrepancies are divisible by `p^a`.
At z the discrepancy is `-2p^a`, with valuation exactly a. Thus trace depth is a,
but the supremum of Hom lengths is `a+3min(a,c)>a`. This is exactly the failure one
expects without integral matrix spanning.

Independent direct enumeration of matrix intertwiners gave the following counts:

| p | a | c | n | Number of intertwiners |
|---|---|---|---|---|
| 3 | 2 | 1 | 1 | 81 |
| 3 | 2 | 1 | 2 | 243 |
| 3 | 2 | 1 | 3 | 243 |
| 3 | 1 | 2 | 2 | 81 |
| 5 | 1 | 1 | 2 | 625 |

All agree with `p^(min(n,a)+3min(n,a,c))`. The algebraic argument is the proof;
these finite computations were a separate check. The example is a matrix representation
of a free group and is not asserted to satisfy the other arithmetic SelmerDatum hypotheses.

## 5. Symmetric finite-depth extension: required checks

For the source conjugate dual, transpose preserves the intertwiner space because
`c^2=1` and `chi(g^c)=chi(g)`. If the residue characteristic is odd, transpose on a
nonzero cyclic `H_n` acts by a scalar epsilon in `(O/pi^s)^*` with `epsilon^2=1`,
where `s=min(n,a)`. In this local ring with 2 invertible, epsilon is exactly +1 or -1.
Its value is determined already modulo pi. Therefore an appropriate finite symmetric
Hom term should be either the full cyclic module or zero, according to this residual sign.

However, an exact statement must specify the chosen definition of symmetry and the
identification of the character pairing. It must not equate the conjugate-dual sign
automatically with the sign of an ordinary self-dual or Weil pairing. The rank-two
symplectic example acquires its conjugate-dual form by an additional conjugation matrix.
The forthcoming extension should be checked against these conventions before claiming
it is exactly a source-defined symmetric term.

## 6. What remains an implementation obligation

The mathematical derivation is complete at the ordinary theorem level. It is not yet a
Lean proof or an upstream patch. A formal implementation must prove the finite character
module identification or an equivalent one-dimensional-socle statement in the repository's
native types; transport O-length through it; prove cyclicity; and replace the isolated
global bound. Exact trace-depth certificates need not be formalized first merely to remove
the rank factor: cyclicity plus the already proved scalar annihilation suffices.

This smaller proof route is preferable for a first upstream-quality refactor. The broader
trace and finite-word theorems add the useful computational interface, but are not logical
dependencies of the scalar-bound improvement.

## 7. Review of the subsequently supplied finite-sign theorem

The formulation in `research/trace_depth_section.tex`, including the dyadic refinement,
is correct. Let `0<a<infinity` and choose a unimodular intertwiner `P` modulo `pi^a`.
The module at that level is free of rank one, so transposition has the form
`P^T=epsilon P`, with epsilon a unit and `epsilon^2=1` modulo `pi^a`.
Set `s=min(a,v_pi(epsilon-1))`. This number is independent of the chosen lift of epsilon,
and also of the chosen generator P because scalar multiplication commutes with transpose.
For `r=min(n,a)`, the finite-level module is generated by
`pi^(n-r)(P mod pi^r)`. Its symmetric part imposes
`(epsilon-1)b=0 mod pi^r`, and therefore has length `min(r,s)=min(n,s)`.

At odd residue characteristic epsilon is +1 or -1. At residue characteristic two the
measured s is essential. The matrices

\[
P_\epsilon=\begin{pmatrix}0&1\\\epsilon&0\end{pmatrix}
\quad (\epsilon=1,3,5,7\bmod8)
\]

are invertible and satisfy `P_epsilon^T=epsilon P_epsilon`, as claimed. They illustrate
finite algebra only, and no arithmetic realization is implicit. Thus the agent's new
formulation correctly handles a caveat not covered by an odd-prime sign dichotomy.

## 8. Review of the Ramanujan Delta arithmetic certificate

The complete argument in `research/delta_congruence_case.tex` is correct. I additionally
checked its classical input in the author-hosted research report

`https://math.leidenuniv.nl/reports/files/2007-34.pdf`, Section 5, printed pages 21--22
(PDF indices 21--22). The report defines exceptional primes by failure of the integral
image to contain `SL_2(Z_l)` and explicitly gives the set
`{2,3,5,7,23,691}`, citing the corollary to Theorem 4 of Swinnerton-Dyer's 1973 paper.
Its Frobenius trace and determinant statements are also present. The manuscript itself
is dated May 11, 2006 despite the server filename `2007-34.pdf`.
My direct fetch of the Chenevier-hosted scan of the original Swinnerton-Dyer paper timed
out; the parent/candidate's successful source inspection should be distinguished from this
second verification.

Restriction to `G_E`, `E=Q(sqrt(-23))`, retains `SL_2(F_l)` because the subgroup image
is normal of index at most two, and `SL_2(F_l)` is perfect for `l>=5`. Every prime in
the proposed range satisfies this lower bound. Hence the full integral matrix-span
condition is justified by residual irreducibility and Nakayama.

Complex conjugation is an integral change of basis since rho extends to `G_Q`.
For a rank-two lattice, the wedge pairing identifies its dual with itself tensor the
inverse determinant. With arithmetic Frobenius and determinant `chi_l^11`, this gives
`D(T_l) ~= T_l tensor chi_l^(-10)`, with precisely the exponent in the candidate section.
Both 2 and 3 split in E, so degree-one places give the discrepancies
`tau(p)(1-p^(-10))`. The integer factorizations and gcd 792 are correct.

For every nonexceptional l other than 11, one of the two discrepancies is a unit, forcing
the global congruence term to vanish. At 11 the discrepancy at 2 has exact valuation one,
while `chi_11^10=1 mod11` provides a group-wide lower congruence. Thus the exact result is

\[
C(T_l)=1\ (l=11),\qquad C(T_l)=0\quad
(l\notin\{2,3,5,7,11,23,691\}).
\]

### Additional sign check

The symmetric refinement does not remove the remaining contribution at 11. Let
`C=rho(c)` for complex conjugation and
`J=[[0,1],[-1,0]]`. We have `C^2=I`, `det C=-1`, and
`C^T J C=-J`. Therefore `P=C^T J` is unimodular and symmetric:
`P^T=-J C=C^T J=P`. For every `g in G_E`,

\[
\rho(g^c)^T P\rho(g)=\chi_l(g)^{11}P.
\]

Modulo 11 this is exactly the conjugate Tate-pairing relation because `chi_11^10=1`.
Hence `C^+(T_11)=1`, and all the other nonexceptional symmetric terms are zero.
After the central Tate shift `j=-5`, the determinant becomes chi and the same construction
gives an exact symmetric conjugate Tate self-duality. Both `C` and `C^+` are then infinite.
This is a useful safeguard against inferring that a symmetric-target refinement bypasses
the central self-duality obstruction for this example.

This arithmetic certificate computes one upstream input. It does not certify the other
SelmerDatum hypotheses, in particular the required nontrivial scalar inertia away from l,
and it does not prove a global Selmer or Bloch--Kato theorem.


## 9. Review of the complete Tate family (final extension)

The final extension in `research/delta_congruence_case.tex` is also correct. For every
nonexceptional prime and integer Tate shift j, put M=10+2j. Then

\[
 C(T_\ell(j))=C^+(T_\ell(j))=
 \begin{cases}
 \infty,&M=0,\\
 1+v_\ell(|M|),&M\ne0\text{ and }(\ell-1)\mid M,\\
 0,&(\ell-1)\nmid M.
 \end{cases}
\]

The key point beyond the two-prime calculation is that the restricted residual
representation admits no nontrivial character self-twist. If an invertible matrix U
intertwines rho_bar with rho_bar tensor psi_bar, then psi_bar is first trivial on
ker(rho_bar), since rho_bar(g)=I there. It therefore factors through the residual
image. Its restriction to the contained SL_2(F_l) is trivial by perfectness. Hence U
commutes with SL_2(F_l), whose centralizer consists of scalars, and the intertwining
identity forces psi_bar=1 on the entire group. This factor-through-the-image step is
included explicitly in the final candidate and avoids a hidden assertion about the
abelianization of the original Galois group.

At level l^n, any equivalence with the twist psi=chi_l^(-M) now has psi=1 mod l.
Determinants give psi^2=1 mod l^n. Since every permitted prime is odd, psi+1 is a unit,
so psi=1 mod l^n. Conversely, this character identity supplies an equivalence. Thus the
congruence depth is exactly the depth of triviality of chi_l^M.

The cyclotomic image on G_E is all of Z_l^times: E ramifies at 23, whereas the l-power
cyclotomic extension is unramified at 23 for l != 23, so the quadratic intersection is
trivial. For nonzero M divisible by l-1, lifting the exponent gives minimal valuation
1+v_l(|M|), attained at 1+l; when l-1 does not divide M, a residue unit witnesses depth
zero. Negative M causes no problem because replacing u^M-1 by u^|M|-1 multiplies it by
a unit. M=0 gives exact self-duality at every level.

The canonical conjugate wedge pairing remains symmetric after each Tate shift: complex
conjugation still has determinant -1, and its square is I. It generates the rank-one
intertwiner module at every allowed congruence depth; multiplication by l^(n-a) handles
higher finite levels if the depth a is finite. Consequently the symmetric term equals
the full term, not just in the unshifted example but for the entire family.

The table of shifts -5,-1,0,1,2,3,4,50 is arithmetically correct. The unbounded-depth
corollary follows by setting M=(l-1)l^(r-1), which is even, so
j=((l-1)l^(r-1)-10)/2 is an integer and yields depth r. This rules out a bound independent
of Tate weight on this congruence input; it is not a statement that all these shifts
satisfy the separate local hypotheses of the upstream Selmer theorem. The final
candidate correctly preserves that distinction.

## Final source and quantifier review

The final report review checked the scope, arithmetic architecture, Euler interface, research program, and validation statements. Two qualifications were incorporated: ordinary local polynomial annihilation applies at the relevant split places away from the coefficient prime and uses geometric Frobenius; and an equality for a common ideal of all Frobenius discrepancies requires an indexing set dense for each local pair. The finite sampled-ideal upper bound needs only the explicitly stated simultaneous unramifiedness assumptions. Arithmetic and geometric Frobenius have the same trace and determinant in the S3 example. No further necessary correction was identified in the reviewed sections.
