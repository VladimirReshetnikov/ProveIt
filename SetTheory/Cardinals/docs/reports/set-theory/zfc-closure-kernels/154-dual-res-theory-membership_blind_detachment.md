# Membership-blind inverse detachment

## Status and purpose

This note proves a change to the *abstract numerical proof calculus*. It does
not, by itself, certify a new Turing-machine transition table. The source
implementation must separately establish the decoder and register contracts
below. Compiler state counts are not part of the mathematical claim.

The change permits an inverse modus-ponens decoder to return arbitrary results
on membership-atom codes. It also permits exact decoding of equality and
universal-quantifier codes without rejecting their tags. The proof uses validity
of closed theorems under **every assignment**, rather than truth under a fixed
assignment. That distinction is essential.

## 1. Exact numerical language

Use the existing native constructors

\[
 P(a,b)=\frac{(a+b)(a+b+1)}2+b,\qquad
 I(a,b)=4P(a,b),\quad R(a,b)=4P(a,b)+1,
\]
\[
 Q(a,b)=4P(a,b)+2,\qquad E(a,b)=4P(a,b)+3.
\]

The target contradiction is \(F=R(0,0)=1\). Native code zero denotes truth.
The exceptional identity \(I(0,0)=0\) is semantically correct because truth
implies truth. Every field of a positive formula code is smaller than its
code, so the usual decoded semantics is well founded. The variable labels in
\(R,E\), and the first label of \(Q\), are the actual natural-number fields;
they are not decoded as formulas in those positions.

Let \(\mathcal T\) be the unchanged native K221/K220 theorem calculus. Retain
truth, the eight native rows (including G), the exact gated V/seed-K bundle,
and theorem generalization.

An **admissible decoder** for this note is any total function

\[
 d:\mathbb N\longrightarrow\mathbb N\times\mathbb N
\]

satisfying

\[
 d(I(a,b))=(a,b),\qquad d(Q(a,b))=(a,b),\qquad
 d(E(a,b))=(a,b).
\tag{D}
\]

There is no condition on \(d(R(a,b))\). In particular, its result need not
encode the fields of the membership atom and need not have any logical
relationship to them.

Replace MP by the following rule, called inverse detachment here:

\[
 \frac{\mathcal T_d\vdash A\qquad \mathcal T_d\vdash H
       \qquad d(H)=(A,B)}{\mathcal T_d\vdash B}.
\tag{ID}
\]

All premises are theorems with no open hypotheses. The modified calculus is
denoted \(\mathcal T_d\).

## 2. The semantic lemma

**Lemma.** Let \(M=(D,\in^M)\) be an ordinary first-order structure with
identity as equality, an irreflexive membership relation, and at least two
distinct elements. Write \(\operatorname{Val}_M(n)\) for validity of the
decoded native code \(n\) under every assignment of natural-number-labelled
variables into \(D\). If \(d\) satisfies (D), then

\[
 \operatorname{Val}_M(A)\land\operatorname{Val}_M(H)
 \land d(H)=(A,B)\quad\Longrightarrow\quad
 \operatorname{Val}_M(B).
\]

**Proof.** If \(H=0\), (D) at \(I(0,0)\) gives \(A=B=0\), and the conclusion
is true. Otherwise split into the four residue classes of \(H\).

* If \(H=I(a,b)\), (D) gives \(A=a,B=b\). For each assignment, the antecedent
  and implication are true, so their consequent is true.
* If \(H=Q(a,b)\), (D) again gives \(A=a,B=b\). Global validity of
  \(\forall v_a\,D(b)\) implies global validity of \(D(b)\): at each
  assignment, take the quantified variable to have its current value. The
  premise \(\operatorname{Val}_M(A)\) is unnecessary in this case.
* If \(H=E(a,b)\) and \(a=b\), the result satisfies \(A=B=a\), so the
  conclusion is precisely the first premise. If \(a\ne b\), assign distinct
  elements of \(D\) to the two variable labels. The equality is false at
  that assignment, contradicting \(\operatorname{Val}_M(H)\).
* If \(H=R(a,b)\), choose any element \(x\in D\) and assign \(x\) to both
  labels \(a,b\), including when they are already the same label. By
  irreflexivity the atom is false. Thus this case contradicts
  \(\operatorname{Val}_M(H)\), regardless of what the decoder returns.

These cases exhaust all native codes. No substitution into an open assumption
or recovery of a weakened equality axiom is used. \(\square\)

The domain assumptions are supplied by every model of ZFC. Foundation implies
irreflexivity. Empty Set and Pairing give two distinct objects, the empty set
and its singleton. Nothing like well-foundedness of the model in the external
metatheory is required.

## 3. Equiconsistency, provably in ZFC

**Theorem.** For every computable decoder satisfying (D), ZFC proves

\[
 \operatorname{Con}(\mathcal T_d)
 \quad\longleftrightarrow\quad
 \operatorname{Con}(\mathrm{ZFC}).
\tag{C}
\]

Here the native K221/K220 calibration is used in exactly the same form as for
the baseline candidate: its formulas and rules are sound in ordinary models
of ZFC, and inconsistency of ZFC yields a native derivation of code 1.

For the forward implication, every ordinary native MP step is an instance of
(ID), because \(d(I(A,B))=(A,B)\). Thus every old native proof translates
unchanged, apart from the name of the inference rule, into a modified proof.
If ZFC is inconsistent, the calibrated old calculus proves code 1, and so does
the modified calculus.

For the reverse implication, reason inside ZFC and assume
\(\operatorname{Con}(\mathrm{ZFC})\). The completeness theorem gives a
set-coded model \(M\) of ZFC. The unchanged native axiom rows and bundle are
globally valid in \(M\), and theorem generalization preserves global validity.
The lemma proves the same for (ID). Induction on finite modified proofs shows
that every modified theorem is globally valid in \(M\). But code 1 is
\(v_0\in v_0\), which is false in \(M\). Consequently the modified calculus
has no proof of code 1. This is a proof in ZFC; it does not assume that ZFC can
prove its own consistency. \(\square\)

The result needed by the machine is only (C). No claim that the two calculi
prove exactly the same native codes is needed for the construction.

## 4. A particularly cheap approximate decoder

Let \(\operatorname{unP}\) be the inverse Cantor pairing function and define

\[
 q_*(h)=
 \begin{cases}
  \max(0,\lfloor h/4\rfloor-1),&h\equiv1\pmod4,\\
  \lfloor h/4\rfloor,&h\not\equiv1\pmod4.
 \end{cases}
\]
\[
 d_*(h)=\operatorname{unP}(q_*(h)).
\tag{A}
\]

This satisfies (D) and is therefore sufficient. It intentionally decodes most
membership atoms using the *preceding* Cantor-pair index.

The encoding experiment identifies a short grouped-decrement loop whose
number of calls to the old Cantor-unpair walk is

\[
 f(n)=\lfloor n/4\rfloor+[n\equiv2\pmod4].
\]

Precede that loop by two guarded decrements of the cached code. Inputs 0 and 1
return the untouched zero pair. For \(h\ge2\), the resulting walk count is
\(f(h-2)\). The four residue cases give

| Residue of \(h\) | \(f(h-2)\), where \(h\ge2\) | Required behavior |
| --- | --- | --- |
| 0 | \(h/4\) | Exact implication fields |
| 1 | \((h-1)/4-1\) | Unconstrained membership case |
| 2 | \((h-2)/4\) | Exact quantifier fields |
| 3 | \((h-3)/4\) | Exact equality fields |

Together with the two short inputs, this is exactly (A). The source-loop
arithmetic claim must be independently checked against the actual compiled
instruction tree; the case table only establishes its mathematical use once
that contract is known.

An alternative uses tags \(I=0,Q=1,R=2,E=3\), target contradiction 2, and the
unprefixed \(f\)-loop. That variant is also covered by the semantic lemma
after the uniform recursive code relabelling. The original-codec version (A)
has the advantage of retaining every axiom emitter and the target constant.

## 5. A simpler complete command interface

For a retained command state \((t,w,d,h)\), where \(w\) is the theorem stack,
let a new command \(\mathrm{IMP}(x)\) first consume the same additive command
field as before, giving \(d'=d+x\), then execute

\[
 (t,w,d,h)\longmapsto
 \begin{cases}
  (B,w,d',0),&d_*(h)=(t,B),\\
  (0,w,d',0),&\text{otherwise}.
 \end{cases}
\tag{M}
\]

In particular there is no dummy stack push and no need to copy \(B\) into the
additive parameter register. The full source contract preserves registers
0 (next proof), 2 (stack), and 8 (remaining proof stream), preserves the value
of register 4 *after the common field reader*, clears cache 5 and scratches
6/7, and leaves selector register 3 zero. Only top register 1 receives the new
theorem (or zero on a failed match).

Every intentionally compiled IMP uses field \(x=0\), so the standard block
contract remains

\[
 \forall T,w,\quad (T,w,0,0)\xrightarrow{L}
 \text{HALT}\quad\text{or}\quad(X,w,0,0).
\]

**Discard.** The one-command block \([\mathrm{IMP}(0)]\) returns
\((0,w,0,0)\) from \((T,w,0,0)\) for every \(T\), because
\(d_*(0)=(0,0)\). If \(T=0\), a successful comparison returns zero; if
\(T\ne0\), a failed comparison returns zero. This replaces the old multi-command
DISCARD sequence.

**Axiom and GEN blocks.** The existing leaf, gated-bundle, and GEN templates
remain valid after replacing each occurrence of DISCARD by this one-command
block. Their stack calculations otherwise do not mention MP.

**Detachment block.** Suppose \(L_A\) builds code \(A\) and \(L_H\) builds
code \(H\), with \(d_*(H)=(A,B)\). Use

\[
 L_A;\ \mathrm{DROP};\ L_H;\ \mathrm{NIP};\ \mathrm{DROP};\
 \mathrm{NIP};\ \mathrm{IMP}(0).
\]

Ignoring an earlier valid halt, the exact state calculation is

| Stage | Current | Stack | Counter | Cache |
| --- | --- | --- | --- | --- |
| after \(L_A\) | \(A\) | \(w\) | 0 | 0 |
| DROP | 0 | \(P(A,w)\) | 0 | 0 |
| after \(L_H\) | \(H\) | \(P(A,w)\) | 0 | 0 |
| NIP | \(H\) | \(w\) | 0 | \(A\) |
| DROP | \(A\) | \(P(H,w)\) | 0 | \(A\) |
| NIP | \(A\) | \(w\) | 0 | \(H\) |
| IMP(0) | \(B\) | \(w\) | 0 | 0 |

If \(A=1\), the second NIP halts, which is already an acceptable proof of
inconsistency. Otherwise the displayed final state follows from (M). Unlike
the old MP block, this block needs no AX/reset/pop suffix.

These three constructions give compilation of every finite modified proof by
induction. As in `L1_Comp222.v`, prepend a fixed AX command to reset the counter
and cache from arbitrary retained state, and append DROP,NIP,NIP to a block
building code 1. The resulting finite command list halts from every retained
state. Its Cantor-pair command encoding is unchanged. Each remaining command
tail decreases between candidate boundaries, so the enumerator eventually
reaches its candidate number unless it halts earlier. The same argument works
from the existing bootstrap seed `(pl=0,np=3,tw=0,ws=0,d=3,h=0)`.

Conversely, the usual invariant says that current, cache, and each stack
element are modified theorems. The semantic lemma validates every successful
IMP; a failed IMP returns the truth code zero. AX, DROP, and NIP preserve the
invariant exactly as before. A NIP halt therefore exhibits a modified proof
of code 1. Subject to the source contract (M), the new enumerator halts iff
ZFC is inconsistent, provably in ZFC.

## 6. Checkable dependencies and remaining implementation gate

The exact source interfaces used above are the repository's `Enum222.v`,
`L1_Comp222.v`, `L1_Sound222.v`, and `Seed222.v` under
`k225-formal/rocq/rocq-extension/coq/221/`. The existing native theory is in
`Codes222.v` and `Thm222.v`; the closed ZFC calibration endpoint is
`CorrectDense221.v` (with the source/theory bridge in `Main222.v`).

Before attaching this argument to a candidate table, establish all of:

1. The literal new source block implements (M), including small cached inputs,
   the arithmetic approximation (A), both comparison outcomes, arbitrary
   preserved registers, and clearing all temporary registers.
2. The complete recompiled source is bound to that modified block and the
   unchanged remaining native source.
3. The decoder/interpreter/blank-bootstrap proof transfers to the actual
   transition table, and its distinct working-state count meets the updated
   target of at most 218 states.

The theorem in Sections 2--3 is complete independently of whether those
implementation measurements meet the state target.

## 7. Disequality corollary: both odd tags may decode arbitrarily

Use one of the calibrated negative-equality variants in
`disequality_codec.md` or `negative_equality_dual_b.md`, respecting their
different row restrictions. Replace MP by inverse detachment using any
total computable decoder d with only the requirements

```
d(I(a,b)) = (a,b),    d(Q(a,b)) = (a,b).
```

Both odd constructors may decode arbitrarily. In a ZFC model, neither a
membership atom nor a disequality atom is globally valid, because an
assignment identifying its two endpoints refutes it. Therefore no odd
cached theorem can satisfy the semantic premises. The implication and
quantifier cases of the preceding soundness proof remain unchanged.
Every ordinary MP inference is still an inverse inference, so the
previous finite contradiction-proof translation gives the other
consistency implication. The parity halt predicate is also still sound,
and its acceptance of F gives completeness.

In particular, `d(h)=unP(floor(h/4))` works without a tag-dependent
logical side condition. An implementation need only be exact on the two
even residues. This does **not** license dropping the two guarded
decrements from the existing thirteen-leaf approximate decoder: its
eleven-leaf loop has count `floor(h/4)+[h mod 4=2]` and is therefore wrong
on quantifier codes. Whether the weaker decoder contract produces a
smaller compiled source is an independent encoding question.
