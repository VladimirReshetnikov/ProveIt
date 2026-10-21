# Fixed public labels suffice for the seed-K schema

This is a theory calibration, independent of whether a proposed source tree
implements the required axiom family or saves a machine state. The native
logical rows, constructors, truth, MP, and GEN remain unchanged.

## Exact retained axioms

Keep every membership-vacuity instance

\[
V(a,b,c)=R(a,b)\to Q_cR(a,b),\qquad c\ne a,b.
\]

Replace the seed-K part of the bundle by the instances

\[
\operatorname{Seed}(0,1,c)=N(\operatorname{nks222}(0,1,c)),
\qquad c>1.
\]

Here the matrix is the native formula whose code is **exactly** `c`, and the
private container binder is also label `c`. In particular, there is no
unproved arbitrary renaming rule for native proof codes. All membership
vacuity must remain available, including private binders 0 and 1. Keeping
only `V(0,1,c)` does not meet this theorem's assumptions.

Call the resulting numerical calculus `C01`. Then

\[
\mathrm{ZFC}\vdash
\operatorname{Con}(C01)\leftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

The same conclusion holds for fixed public roles `(1,0)`; the existing
`Complete222.v` proof already supplies fixed roles `(1,3)`.

## Why the pure-logic bridge is retained

`Interp222.v` first projects arbitrary membership vacuity from the old
bundle, then invokes it in `lprov224_thm222`. Its other logical ingredients
are the unchanged rho rows, G, MP, and GEN. `G222.v` derives equality
reflexivity, the special equality helper, and rho7 from G, rho1, rho2, rho6,
and propositional logic alone. `L224E.v` interprets full equality as
membership indiscernibility. Consequently retaining all V gives, with no
appeal to any seed-K axiom,

\[
\operatorname{lprov}(A)\Longrightarrow C01\vdash\tau(\operatorname{th}(A)).
\]

This is the same interpreted full first-order logic used by
`Complete222.v`. It justifies ordinary capture-avoiding substitutions and
alpha equivalence in the following argument. It does not assume that an
arbitrary permutation literally maps a native K axiom to another native K
axiom: the private binder/code coupling is handled afresh below.

## Exact replacement of the source-name translation

For a de Bruijn matrix `phi`, define

\[
\eta_{01}(0)=1,\qquad \eta_{01}(1)=0,\qquad
\eta_{01}(n+2)=2n+5.
\]

Index 0 is the output and index 1 the input. The remaining indices are
parameters. This is injective. All its values are distinct from the positive
even binder names used by `Std_tr` (`bname(k)`), including its exceptional
value 0. Thus the proof of `ordinary_matrix230_equiv` works with `eta01`:

\[
\mathrm{EqAx}\vdash
dB_\rho(\operatorname{tr}_{\eta_{01}}\phi)
\leftrightarrow
\phi[n\mapsto\rho(\eta_{01}(n))].
\]

The relevant hypothesis of `tr_equiv` is disjointness of free source names
and binder names. Positivity of all source names is **not** used in this
bridge. Positivity appears in the separate older numerical-decoder lemma
`ordinary_code230_decode`, through `no_relative_atom`; `Complete222.v`
bypasses that lemma by constructing its seed code directly with `tau`.
That distinction permits input label 0 here.

Define

\[
q_\phi=\neg\neg\operatorname{tr}_{\eta_{01}}\phi,
\qquad
c_\phi=\tau(\operatorname{th}(q_\phi)).
\]

The existing `seed_code_gt3` arithmetic proves `c_phi>3` unchanged. The
existing `tau_fr` and `th_fr` proofs likewise show that label `c_phi` is not
free in the translated matrix. These are direct syntactic code bounds;
they do not depend on how the free source names were chosen.

The fixed-role axiom is now literally

\[
C01\vdash \operatorname{Seed}(0,1,c_\phi).
\]

Using the same `tau_th_SeedN` expansion as the baseline and the retained
membership-vacuity axiom `V(0,1,c_phi)`, propositional conjunction gives

\[
C01\vdash
\tau\bigl(\operatorname{th}
  (\operatorname{SeedN}(0,1,c_\phi,q_\phi))\bigr).
\]

The private variable of this emitted formula is its **new actual matrix
code** `c_phi`; it is not an old private label carried through a numerical
renaming. This explicitly addresses the code/binder coupling.

## Environment equations and the K bridge

For a parameter environment `sigma`, output object `x`, and input object
`a`, put

\[
e^{01}_{\sigma,x,a}(v)=
\begin{cases}
x,&v=1,\\
a,&v=0,\\
\sigma(\lfloor(v-5)/2\rfloor),&\text{otherwise},
\end{cases}
\]

where natural subtraction is truncated. At the named parameter indices
`2n+5`, the last clause returns exactly `sigma(n)`. Thus

\[
e^{01}_{\sigma,x,a}(\eta_{01}(n))=(x,a,\sigma)_n.
\]

Define the private environment by updating coordinate `c_phi` to the
container object `C`. The precise replacements of the `KDecodeEnv.v`
equations are:

* Updating output coordinate 1 changes `x`, preserving `a` and `C`.
* Updating input coordinate 0 changes `a`, preserving `x` and `C`.
* Updating coordinate `c_phi` does not change matrix truth, because that
  coordinate is fresh in the matrix.
* `R(1,c_phi)` becomes `x in C`.
* `Q_c_phi(R(c_phi,0) -> R(c_phi,1))` becomes `a subseteq x`.

Every equation follows by direct substitution and `c_phi>3`; the first two
actually need only `c_phi>1`. The matrix equivalence above becomes

\[
dB_{e^{01}_{\sigma,x,a}[c_\phi:=C]}
    (\operatorname{tr}_{\eta_{01}}\phi)
\leftrightarrow\phi[x,a,\sigma].
\]

Substituting these equations into the literal seed formula is precisely the
proof of `named_seed_to_seeded` in `Complete222.v`, with output label 3
replaced by 1 and input label 1 replaced by 0. The result is the same ordinary
`seeded_core(phi)`. The normalization of the double-negated matrix is the
existing purely logical `L_seed` argument. The support conjunct and subset
closure are both retained; nothing is weakened or omitted.

The rest of the old chain is unchanged: `seeded_core_to_kp0` yields each K0
schema instance; the existing K0 interpretation yields inconsistency of
`C01` from inconsistency of standard ZFC. This translation is effective and
all of its inductions are formalizable in ZFC.

For the opposite direction, a model of ZFC validates every retained logical
row and V instance, and every fixed-role seed instance whose private label
is fresh. The direct code bound ensures freshness for every native matrix
code `c>1`, not only the specially padded matrices used for completeness.
Therefore Con(ZFC), the completeness theorem, and proof induction imply
Con(C01). Together these give the stated internal equiconsistency.

## The two small codes and source gating

For roles `(0,1)`, the only potentially colliding matrix/private labels are
0 and 1. Their actual native matrices are truth and falsum, respectively.
They must not be treated as arbitrary formulas in this analysis.

* At `c=0`, the literal seed formula is false in ZFC. The matrix is truth;
  its request `w` says that coordinate 0 is nonempty, the subset guard is
  always true by irreflexivity, `u` says every set is nonempty, and `h` says
  the container is empty. The outer seed demands an empty and nonempty
  container simultaneously. Thus a source implementation must suppress or
  replace this instance.
* At `c=1`, the matrix is `R(0,0)`, which is false. For roles `(0,1)`,
  `w=u=h=true`, so the seed is true. It may safely be emitted despite its
  private/output label collision. For swapped roles `(1,0)`, `w=u=true` and
  `h` says the container is empty; the seed is again true by the empty-set
  axiom.

Hence a K-only zero test suffices for soundness of roles `(0,1)` or `(1,0)`.
This does **not** license suppressing membership vacuity at private binder 0:
the retained V family is a separate hypothesis. A source can emit V alone
in the zero-code branch and V together with the fixed-role seed otherwise,
subject to its ordinary V freshness checks. Exact source realization and
state cost remain separate obligations.

## False-code roles remove the additional K gate

There is a useful stronger version for source construction. Fix public
labels `a=1,b=8`, or swap them. Native code 1 is F and native code 8 is
`I(0,F)`; both formulas are false in every model of ZFC under every
assignment. Then **every** instance `Seed(1,8,c)` is ZFC-valid, with no
restriction on `c`.

If `c` differs from 1 and 8, the usual code-label bound makes the private
label fresh and the ordinary seed-K soundness proof applies. If `c=1` or
`c=8`, the matrix is false, including under every binder occurring in the
template. Expanding the literal template gives

\[
w=\top,\qquad u=\top,\qquad
h=\forall b\,\neg R(b,c),
\qquad
\operatorname{Seed}=\exists c\,\forall b\,\neg R(b,c).
\]

If `c!=b`, the last formula is existence of an empty container, valid in
ZFC, including when `c=a`. If `c=b`, the atom in the last universal is
`R(b,b)`, so irreflexivity makes the last formula true. There is no appeal
to generic freshness in either collision case.

Completeness uses exactly the old fixed-role `(1,3)` translation followed by
the bijection `pi` swapping named labels 3 and 8 and fixing every other
label. Apply `pi` uniformly to **all named variable occurrences and
binders** in `tr(source_names,phi)`, before applying `th` and `tau`:

\[
t^{18}_\phi=\pi\mathbin\cdot\operatorname{tr}_{\eta_{13}}\phi,
\quad q^{18}_\phi=\neg\neg t^{18}_\phi,
\quad c^{18}_\phi=\tau(\operatorname{th}(q^{18}_\phi)).
\]

The old output name 3 becomes 8 and input name 1 stays 1. When old binder
name 8 occurs, it becomes 3. Thus no capture is introduced; merely changing
the free-name function while retaining binder name 8 would be wrong.
The direct code bound again proves that the newly recomputed private label
is fresh. Moreover the two outer negations give `c_phi>=184>8`: for any
`n>=0`, `N(n)=4P(n,1)>=8`, and `N(N(n))>=4P(8,1)=184`.

For an environment `rho`, structural induction gives

\[
dB_\rho(\pi\cdot A)=dB_{\rho\circ\pi}(A).
\]

Use `source_env18(v)=source_env13(pi(v))` and update its fresh private
coordinate to the container. Since `pi` is an involution and fixes
`c_phi>8`, the old source-environment and private-environment equations
transfer literally. The old proof of `named_seed_to_seeded` therefore
applies, with labels `(1,8)` replacing `(1,3)`. As before, full interpreted
logic is retained by the unrestricted V family. This proves the same
internal consistency equivalence.

Consequently a modified emitted conjunction

\[
V(a,b,c)\land\operatorname{Seed}(1,8,c)
\]

can use the original V gate `c!=a,b` without an additional K gate. Both
projections remain available: every legal V instance is emitted with a
sound seed conjunct, and for any `c` one can choose fresh original V
endpoints to obtain the seed conjunct. The family using swapped fixed roles
`(8,1)` has the same proof after swapping the input/output naming convention.

More generally, fixed distinct public labels `p,q` whose own native
formulas are false in every ZFC model have the same collision property.
The labels need not be bounded constants for soundness: parameters can be
mapped into a family of always-false formula codes, such as
`N(I(x,x))`. For completeness, such a parameterization must still realize
two chosen distinct public labels independently of the matrix, so that
arbitrary translated seed instances remain available. Choosing fixed
labels 1 and 8 avoids a further parameterization argument.

## Kernel status

This is a complete mathematical adaptation of the checked baseline proof
interfaces. No new Rocq file has been compiled, and no claim is made that
merely changing constants in `Complete222.v` compiles without adapting its
environment lemmas and theorem definitions.
