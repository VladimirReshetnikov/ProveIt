# Diagonal vacuity: a smaller source program with the same arithmetic calibration

## Status and scope

This is a source-program reduction, not a claim of a machine below 196 states.
The verified concrete realization currently packaged by the physical-table agent
has **199 working states**, a binary alphabet, zero blank, and a separate halt
state. It has 191 AX macro tokens and 3,700 primitive register instructions,
compared with 201 and 3,812 for the pinned 196-state predecessor. The shorter
program has not yet yielded a smaller physical decoder.

The mathematical change has a complete ordinary proof. Its new proof templates
have not been added to the predecessor's Lean PA-certificate compiler. The
literal 199-state realization has passed the full Python symbolic runtime
checker and exact blank-tape startup check. Those claims should remain distinct.

## Pinned predecessor

- Repository: <https://github.com/jamesyc/BusyBeaver>
- 196-state commit: `407cdc356f6b586635e71ac92be394255f4bfea4`.
- Historical 209-state commit: `69d98241a721ead20b4f0b17df9062950b40fbfe`.
- The precise predecessor source is `PA196/Program.lean`, with its symbolic
  command emitter in `PA196/Source/AXProgram.lean` and
  `PA196/Source/AXSymbolic.lean`.
- Relevant mathematical interfaces are `PA196/Logic/Reverse.lean`,
  `PA196/Logic/Neighborhood.lean`, and Sections 3–4 of `paper/pa196.tex`.

The earlier 209-state program has 3,948 physical source sites; the 196-state
program has 3,812. The 196-state change reverses the arguments used by the
universal-quantifier constructor and replaces a seventh equality-related head
with equality vacuity inside the guarded gate. This new construction replaces
that equality-vacuity clause by a diagonal schema.

## Constructors and the new gate

Use the predecessor's constructors, without changing the numerical coding:

\[
 p(a,b)=\binom{a+b+1}{2}+b,\qquad
 I(a,b)=4p(a,b),\quad M(a,b)=I(a,b)+1,
\]
\[
 U(a,B)=I(B,a)+2,\qquad E(a,b)=I(a,b)+3,
 \qquad N(B)=I(B,1).
\]

Every variable label appearing in the formula decoded from a positive code
\(B\) is smaller than \(B\). Code zero is truth. Thus the following formula is
valid for every natural-number formula code \(B\), including zero:

\[
 \Gamma(B)= B\longrightarrow U(B,B).
\]

Keep the six unguarded axiom heads, the restricted propositional head, the
saved generalization, every outer command, and the original freshness guard.
Inside AX, replace only the old equality-vacuity conjunct by \(\Gamma(A)\).
With the predecessor's membership-vacuity clause \(V\) and separation tail
\(Q\), the new gate is

\[
 F_{\rm diag}(H,D,A)
   =N\bigl(\Gamma(A)\to(V(H,D,A)\to Q(H,D,A))\bigr).
\]

It is emitted when \(A\ne H,D\), and the command emits truth otherwise.
Classical propositional reasoning extracts both \(\Gamma(A)\) and the old
membership-vacuity/separation gate \(N(V\to Q)\). For every desired formula
code \(B\), choose \(A=B\) and \(H=D=B+1\). This satisfies the guard and
therefore supplies the unrestricted schema \(\Gamma(B)\).

## Exact emitter change

The old equality clause occupies zero-based macro-token interval `[121,138)`:
17 tokens. Replace it by

```
copyA copyA copyA cons incT incT cons
```

Each `copyA` saves the current accumulator and loads parameter A. `cons`
replaces the top saved item and the accumulator by their `I` constructor.
The seven-token sequence saves the preceding head, then computes

\[
 I\bigl(A, I(A,A)+2\bigr)=\Gamma(A).
\]

The final two conjunction constructors and outer negation remain in their old
positions. Consequently the command still pushes exactly nine items, including
the saved top. The nine stack expressions are identically the same as before;
only the final guarded accumulator formula changes. The cleanup still sets
\(d=h=0\).

The old 17-token clause expands to 246 primitive instructions; the new clause
expands to 134. This gives a reduction of 112 primitive instructions, hence
3,812 to 3,700, and 201 to 191 macro tokens. The AX ordinal interval changes
from `[50,3693)` to `[50,3581)`; all 169 instructions outside AX are unchanged
apart from relocation of their addresses.

`diagonal_semantics.py` checks the emitter in the free algebra of formula
constructors, not by testing a collection of numerical inputs. Its generated
`diagonal_semantics_receipt.json` contains the exact nine stack expressions,
new gate expression, token list, source hashes, and numerical counts.

## Why diagonal vacuity supplies the missing equality argument

Retain the predecessor's two direct membership rewrites and its membership
vacuity schema. The latter is closed under negation, implication, and
quantification away from the free labels, using the same existing logical
heads.

The only delicate point is reverse rewriting. Let

\[
 C=E(a,b)\to\bigl(\chi(b)\to\chi(a)\bigr),
\]

where \(\chi(t)\) is one of the membership atoms used in the predecessor's
reverse-rewrite lemma. Assume the same noncollision conditions used in its
first case; its diagonal cases are then recovered by the same two-step
membership rewrites. Set

\[
 \varphi=N(C),\qquad c=\operatorname{code}(\varphi).
\]

This code exceeds all labels in \(C\), so the pointed-separation gate at
\((a,a,c)\) satisfies the freshness guard. It gives
\(\exists x_c(S\wedge P)\), where \(P=\varphi\to M(c,a)\), and

\[
 S\to U\bigl(a,M(c,a)\to\varphi\bigr).
\]

Propositionally, \(\varphi\to N(\chi(a))\). Therefore weaken the last
consequent before using the predecessor's negative-property specialization
lemma. That lemma only transports membership atoms, so it gives

\[
 S\to\bigl(M(c,b)\to N(\chi(b))\bigr).
\]

This is why there is no need to substitute through the primitive equality
atom occurring inside \(\varphi\).

Under \(\varphi=\neg C\), the formulas \(E(a,b)\), \(\chi(b)\), and
\(\neg\chi(a)\) hold. The point clause gives \(M(c,a)\); the direct
membership rewrite gives \(M(c,b)\); and \(S\) then gives
\(\neg\chi(b)\), a contradiction. To discharge the existential separator,
use the extracted diagonal instance

\[
 \Gamma(\varphi):\quad\varphi\to U(c,\varphi).
\]

It supplies exactly the vacuity needed for the outer contradiction argument.
Equivalently, negation closure and double-negation elimination make \(C\)
vacuous at \(c\), and the usual existential-elimination template yields \(C\).
This proves both reverse membership rewrites. Unlike the predecessor's
choice \(\varphi=\neg\chi(a)\), the new choice automatically avoids every
label collision; no padding branch is required.

For the defined equality relation, first let
\(z_0=\operatorname{code}(E(a,b))\). The diagonal instance for \(E(a,b)\)
and the direct/reverse membership rewrites give

\[
 E(a,b)\to R(a,b,z_0).
\]

Here \(z_0>a,b\). The two matrices defining \(R\) contain only membership
atoms. Their quantifiers can be renamed from \(z_0\) to any
\(z\ne a,b\), using the equality witness, the two membership rewrite
directions, and membership-only vacuity. If \(z=z_0\), use the formula already
obtained. Thus the full predecessor interface is recovered:

1. Both membership rewrite directions.
2. \(E(a,b)\to R(a,b,z)\) for every \(z\ne a,b\).
3. The unchanged existential equality witness.

These are precisely the three interfaces used in the predecessor's PA-proof
transport in place of the removed equality head. All steps are fixed finite
proof templates and arithmetic manipulations of finite formula codes; their
proof compilation is primitive recursive and formalizable in PA. The new
diagonal axiom is itself a PA-provable logical vacuity instance. The standard
syntactic soundness translation outlined in `internal_equivalence_note.md`,
paired with these completeness templates,
gives the same arithmetic calibration at the mathematical level.

The independent fuller proof is in `ipra_analysis/diagonal_vacuity_proof.md`.

## Concrete machine and verification artifacts

The stable 199-state realization is in
`proveit_analysis/diagonal199_final/`:

- `machine.tm`: compact binary table; start 0, halt 199, 398 rows.
- `machine.native.tm`: the same table using inherited sparse native labels.
- `source.tree.json`: the full 3,700-instruction source tree.
- `ax_macro_tree.json`: the 191-token AX tree.
- `dense_labels.json`: the relabeling certificate.
- `folds.json`: the four accepted physical-reader folds.
- `receipt.json`: exact source-CFG audit, symbolic replay, startup, hashes.

The concrete table passes all 4,815 symbolic primitive cases over arbitrary
register contents and all allowed padding lengths. Its maximum abstract
microtrace length is 515. The inherited unary register engine rows are retained.
Its blank-tape startup reaches the same clean-store frame after 58,154 literal
steps. The compiler also checks each macro's exact ordinal CFG and every
relocated outer-program edge.

The compact-table SHA-256 is
`6c29db7f324a0d18ee7dc5bfaa3f9b734011c453586d0bc1b96754a6bab4e52c`.
The 199-state candidate therefore is a reproducible construction; it does not
satisfy the requested strict bound of fewer than 196 states.

## Other valid source transformations explored

A separate safe negation peephole replaces `push; incT; cons` by
`drainTtoX; incT; pair4`. It changes \(t\) to \(4p(t,1)\) while leaving the
stack unchanged, reducing each such occurrence from 47 to 20 primitive
instructions. Applying it to all eight occurrences reduced source size by 216,
but its simplest physical realization needed 197 states. Thus primitive
instruction count is not a reliable proxy for the number of shared decoder
states.

An existential diagonal variant,
\(\eta(B)=(\exists x_B B)\to B\), is another sufficient replacement.
Contraposition gives vacuity of \(\neg B\) at the label \(B\); use
\(B=\neg C\) and \(B=\neg E(a,b)\) in the two arguments above. Its emitter
is longer but shares some existing negation subtrees. No better concrete state
count was found from this variant in the present search.

## Final interface audit

A direct search for `equalityVacuity`, `eqVacuity`, and `deltaVacuity` through
`PA196/Logic`, `PA196/Arithmetic/Certificates`, and
`PA196/Arithmetic/Transport` found uses of equality vacuity only in the two
families replaced above: `Reverse.lean` and `Neighborhood.lean`. Each has a
logical version and an arithmetic-certificate version. The remaining matches
are the definition and its axiom-audit printout in `Vacuity.lean`. In particular,
there is no additional direct use in the transport modules.

Two freshness details deserve precision. In the diagonal membership family
`chi(t)=M(t,t)`, an auxiliary name `d` is unused; the separator code need not
exceed that irrelevant number. The proof only needs the bounds on labels that
actually occur. Also, the target neighborhood binder may be zero. The derived
negation-vacuity lemma works at every label, so the syntactic use of formula
code 1 as falsity does not impose an extra condition `z != 0`.
