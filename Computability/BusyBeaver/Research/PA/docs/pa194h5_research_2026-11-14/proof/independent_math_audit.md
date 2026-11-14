# Independent mathematical audit of PA194H5

## Conclusion

The coefficient-five calculus and the H controller compose correctly at the
level of ordinary mathematical proofs. The argument establishes the
PA-provable biconditional between a finite blank-tape halt of the delivered
machine and a PA refutation. The delivered finite source/table certificates
have been replayed successfully, including independent symbolic execution of
the literal transition table. These finite computations establish the
certificate premises; they introduce no consistency assumption.
No new end-to-end Lean or Rocq endpoint is claimed.

The full argument is written in `pa194h5_calibration.tex`. It supplies the
logical transfer, the total interpretation of all natural codes, the complete
H command compiler, the exhaustive scheduler argument, and the physical
finite-trace endpoint. It uses the supplied ordinary coefficient-four
separate-head PA calibration and the explicit generic restricted-implication
proof template as established research dependencies; it does not mistake the
upstream one-way PA196 Lean theorem for a two-way theorem.

## What was independently checked

I read the coefficient-five calibration and the H/H6 controller proofs, the
complete symbolic command checker, and the exact source/table receipt. I
replayed the H6 symbolic command-word identities after changing the numerical
residue interpretation to modulus five; all identities passed. The replay
receipt is `h5_parametric_word_receipt.json`. This replay is an explicit
parametric use of the supplied certificate, not a claim that a new independent
proof assistant checked it.

The arithmetic facts used by those command identities are independent of
whether the coefficient is four, five or six:

- `I(a,b)=0` exactly when `a=b=0`.
- Implication is injective in its two arguments.
- An implication code has residue zero, whereas `U(i,a)` has residue two and
  is positive; these residues are distinct modulo five.
- Every newly generated AX head and the gate are different from one.
- Cantor pairing has exact total projections, including `P(0,0)=0`.

No proof step requires five to be prime, four to be even, or formula codes to
occupy all residue classes. The physical coefficient change does require its
own source-loop proof; merely changing a numeral in the old four-increment
lemma would not suffice. The delivered source binding supplies the needed
connection to the five-increment body.

## Logical recoding and the diagonal binder

The correct coefficient change recodes numerical labels hereditarily, not
just the exterior formula constructors. Define F(0)=0 and, for n>0 with
n=4P(a,b)+r, define F(n)=5P(F(a),F(b))+r. All components are smaller than n.
A similarly recursive left inverse J, which maps unused residue four to
zero, proves J(F(n))=n. Hence F is injective and fixes the false code one.

Applying this same F to all variable labels preserves binding and the guarded
inequalities. Crucially it gives

`F(Gamma_4(B)) = Gamma_5(F(B))`.

A formula-only recoder with unchanged labels would fail at this point. The
proof does not use such a recoder.

F is not monotone: 40<44, but F(40)=75>55=F(44). Therefore the numerical
restriction on the propositional head is not preserved by blindly recoding
a restricted axiom. The supplied `RestrictedImplication.lean` theorem
`rho8All` is a finite proof constructor that removes this restriction. Its
only order premises are reflexivity and preservation under placement into
either implication component; both follow from a,b<=I_5(a,b). Expanding a
restricted source leaf with this template removes the monotonicity problem.
The relevant generic source was inspected directly.

## Residue four and syntax-level PA soundness

The coefficient-five decoder interprets every positive residue-four code as
closed truth. This is necessary: arbitrary command parameters can introduce
such codes even though the hereditary image of coefficient four avoids them.
The other residues translate to implication, finite binary membership,
universal quantification and equality.

Strict component descent proves that every source variable label in the
translation of B is below B. Residue-four truth introduces no variables.
Thus the diagonal label B is fresh. The numerical alias I_5(0,0)=0 is
handled by a fixed PA proof of the equivalence between truth and truth
implying truth. Auxiliary variables in the bit definition must be renamed to
avoid capture; they are not new free source labels.

Pointed separation is interpreted by finite binary comprehension in PA.
This is a proof-producing syntax operation: it inserts the supplied formula
into a fixed induction pattern. It does not decide that formula, invoke a
truth predicate, or assume reflection for PA. The a=b label-collision case
uses the separate matrix described in the supplied calibration, because
inside that binder the antecedent is Bit(z,z), not a membership predicate
with a supposedly free first argument.

Consequently every C5 proof of one can be transformed into a PA refutation,
and every PA refutation can first be transformed into a C4 refutation and
then recoded into C5. Both transformations and their correctness are
primitive recursive and PA-verifiable.

## The H controller's nontrivial compiler requirements

The H controller halts on cached H=1. Successful MP leaves the stack alone
and returns `(b,w,b,0)`. The compiler must respect both changes.

The ten-entry AX identities give:

- Push = AX(0); Shift^9; MP(0).
- Pop = AX(0); Shift^11; it halts exactly when the saved current top is one.
- Discard = MP(0), valid with arbitrary old cache when the offset is zero.
- Offset(i) = MP(i), including i=0.

The finite MP compiler reserves a zero before compiling either premise.
Its suffix then starts with stack `[a,I_5(a,b),0;w]`; it exposes the premises,
performs no-push MP, and consumes precisely the reserved zero. Omitting that
reservation would consume an arbitrary old stack entry and invalidate the
compiler invariant.

A proof of one is closed by a final Pop, not a final Shift. In fact
`Shift(1,0,0,0)=(0,0,0,0)` for this controller. The full word
`AX(0); compile(proof); Pop` halts from every incoming store. This
arbitrary-store statement is essential because the scheduler carries its
store from one candidate to the next.

The aliases P(0,0)=0 and I_5(0,0)=0 are checked explicitly; the proof does not
pretend the numerical stack is a free list. Soundness annotates both visible
formula registers and every canonical stack entry. No formula-derivability
invariant is imposed on the offset register.

## Exact source and physical scope

The construction receipt identifies a complete 194-state, 388-row machine,
with 202 raw controls and eight folds. Its source has 3,714 sites and 4,815
branch-sensitive outcomes. The source binding restores all 61 multiplier
blocks from five increments to four and obtains the original H source graph,
including all outside successor edges. The 3,409 outside sites are unchanged.

The current construction receipt reports all 4,815 symbolic contracts passed,
and a complete blank startup after 58,088 transitions. These are universal
symbolic contracts over the stated frame parameters, not samples of small
register values. The separate literal-tape replay passed all 4,815 outcomes,
four list lemmas, whole-tape blank startup, and dense/native conjugacy, using
1,121,654 symbolic operations. Its longest outcome used 403 symbolic operations
and every outcome has positive duration (minimum constant term three). The
receipt is `../machine/independent/receipt.json`. The integrated replay also
passed exact rebuild equality, source binding, command words, and novelty
comparison against 76 earlier transition graphs.

Positive durations justify both directions of physical/source halting
transfer. If a physical run first halted at time T while the source had not
halted, the first T+1 certified positive source blocks would provide a longer
nonhalting physical prefix, contradicting determinism. This avoids relying on
unproved global absence of halting.

The dense table inspected has SHA-256
`417e3940a77a6222ccd06885209cc853e572ac48b64acbabf581942f142304c9`.
The native table inspected has SHA-256
`4448d94a91c04443a34b1d99015c13ee514fd1a9d2cff091616eb60aeece726e`.

## Claim boundary

PA194H5 is a new verified composition of existing ideas at 194 states. It is
not a sub-194 construction or a new axiomatization of PA, and this audit does
not assert global state minimality. The PA-provable biconditional is the
mathematical result. Actual nonhalting is the additional external consequence
under consistency of PA; PA is not claimed to prove its own consistency.
