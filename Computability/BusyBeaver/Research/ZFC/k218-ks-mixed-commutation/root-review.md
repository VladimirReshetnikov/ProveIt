# Independent review of the mixed-commutation calibration

Reviewer: root, 20 October 2026. Reviewed the complete frozen `proof.md`
(SHA-256 `372d79ddfb4ab8eda23bffac6e57e59101c4d224b7a49c7ae798f571b6dd2702`),
the earlier K/S+QS proof's infrastructure, and the new finite bridge builder
and inherited Hilbert validation routine. No mathematical defect was found.
This is an ordinary proof review; I did not rerun the bridge builder or a
proof assistant.

The new calculus replaces unrestricted rho8 by K and S, replaces rho4 by
`Q_i NN(Q_j A) → NN(Q_j(Q_i A))`, and retains every other native row,
truth, MP, theorem-only GEN, and the exact gated bundle. The conclusion is
equivalence of finite refutability, not pointwise equivalence of derivability.

The central step co-translates numeric variable labels and formula codes.
The strong recursion has strictly smaller constructor arguments for every
positive native code, while zero is handled before decoding. The implication
law also holds at `I(0,0)=0`. The image has neither a raw Q head nor the form
`N(Q_i X)`, which separates the translated Q case from the translated I
case. Together with the zero case and constructor inversions this proves
injectivity and transports the literal bundle inequalities. It preserves
the matrix/private-label identity without an unproved renaming principle.

Atomic stability uses only retained rows and K/S; its proof does not use
rho4 or quantified stability. Consequently structural induction proves
stability of every translated code, although arbitrary original Q codes
need not be stable. This distinction supplies translated rho8 without
assuming the missing full classical basis. Translated rho6 reduces by
triple-negation equivalences, and translated rho2 follows from normality
and the intuitionistic preservation of MP under double negation. The
merged G binder is preserved literally. Truth, MP, and GEN transport with
the final GEN double-negation introduction acting on a closed theorem.

For rho4 the new mixed row is first lifted through double negation; normality
then inserts the remaining inner double negation. The bundle proof keeps
the doubled subset/requirement terms and both repeated quantifiers in the
closure. Its two contravariant negation steps give `clos → translated clos`,
so the inner core arrow runs in the opposite direction. The resulting
`translated core → NN native core`, together with the native bundle's
double-negated persistence and negated core, yields the translated bundle.
No quantifier stability, hidden open GEN, or arbitrary matrix/binder
decoupling is used.

The reverse refutation translation uses the accepted original calculus's
classical basis to derive K, S, and the new mixed row. Both constructions
are finite proof transformations, with a primitive-recursive co-translation
and course-of-values induction formalizable in PA. Thus the ordinary proof
calibrates the new theory to the accepted native calculus and hence to ZFC.

The finite bridge check supports seven local conditional arrows only; it
does not itself verify the all-natural injectivity or proof-translation
metatheorems. No Lean theorem, new enumerator, smaller transition table,
runtime simulation, or blank-start proof is certified by this review.
