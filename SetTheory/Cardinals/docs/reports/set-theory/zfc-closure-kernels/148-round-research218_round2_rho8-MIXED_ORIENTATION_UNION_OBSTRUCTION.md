# New extension: even the union of all six fixed membership orientations is consistent

Date: 2026-10-20. Status: ordinary mathematical proof, independently reviewed PASS in `../research217_theory_review/MIXED_ORIENTATION_UNION_INDEPENDENT_REVIEW.md`; not formalized in a proof assistant. The independent review pins the pre-status-update text hash; only this status sentence changed afterward. It extends the invariant at upstream commit `7c3bca89c19b3a33eab255cb8b6ff2a31bc50fcc`; the upstream publication itself explicitly stopped at separate fixed orientations.

## Statement

Keep every retained native K219 row and the exact full seed/support bundle, truth, MP, and GEN. Admit all six rho8 families with fourth argument one of

`R(a,b), R(b,a), R(a,c), R(c,a), R(b,c), R(c,b)`.

The resulting union calculus is still consistent by a finite syntactic invariant formalizable in ZFC. Consequently the suggested `bc+ab` and `bc+ca` unions do not repair consistency calibration. This conclusion uses literal numeric-code schemas, not a theorem-substitution principle.

## Expanded invariant

Partition the six builders into the first-parameter-dependent family

`V_s(a,b,c) in {R(a,b),R(b,a),R(a,c),R(c,a)}`,

all satisfying `V_s(a,b,c)>a`, and the two last-parameter builders

`W_0(b,c)=R(b,c)`, `W_1(b,c)=R(c,b)`,

both satisfying `W_t(b,c)>c` and `W_t(b,c)=1` iff `b=c=0`.

For each t in {0,1}, define

`p_t(b,c)=I(c,W_t(b,c))`,

`J_t(b,c)=I(I(p_t(b,c),c),I(b,c))`.

For each ordered pair t,u in {0,1}, put

`a_tu(b,c,d)=W_u(d,p_t(b,c))`,

`h_tu(b,c,d)=I(I(a_tu(b,c,d),c),I(b,c))`,

`D_tu(b,c,d)=I(I(h_tu(b,c,d),p_t(b,c)),I(d,p_t(b,c)))`.

Let S be generated, without MP, by the retained rows, all full bundles (or the stronger arbitrary-Q-core bundle family), all six H families, identities, GEN, quantified monotonicity, both J families, and all four mixed D families.

The root-tag, Q-stripping, and three forbidden-shape lemmas from `UPSTREAM_FIXED_ORIENTATION_CLOSURE_REVIEW.md` survive unchanged: every new H/J/D has I-headed immediate antecedent and consequent. In particular the exact full seed/support core is retained.

## 1. Majors whose fourth argument contains a

Consider an H major with `v=V_s(a,b,c)>a`. Its minor must be `I(I(c,v),a)`.

- Identity would give `a=I(c,v)>=v>a`.
- Any H minor, of any of the six orientations, has shape `I(I(I(z,U),x),I(I(x,z),I(y,z)))`. Matching forces `x=v` and `a=I(I(x,z),I(y,z))>=x=v>a`. This contradiction is independent of the minor's orientation.
- A J_t(y,z) minor forces `z=v` and `a=I(y,z)>=z=v>a`.
- A D_tu(y,z,e) minor forces its I-headed p_t(y,z) to equal v, a membership code.
- A bundle minor forces its Q-headed core to equal v.
- GEN and all remaining retained rows/monotonicity fail by outer or antecedent tags, except rho6.
- Rho6 forces v=1 and `c=Q_i I(Q_i a,1)`. For the ab/ba orientations this forces a=b=0, so the H conclusion is the admitted identity `I(I(0,c),I(0,c))`. For ac/ca it forces a=c=0, contradicting Q positivity.

Thus these four major families still yield nothing outside S, despite the added other orientations and mixed auxiliaries.

## 2. Last-parameter majors and cross-orientation H minors

For an H_u(a,b,c) major using W_u, its required minor is `I(p_u(b,c),a)`.

Identity gives J_u(b,c). J_t minors are impossible: matching gives `c=p_t(y,z)>=z=W_u(b,c)>c`. D_tu minors equate an I-headed p_t with W_u. Rho6, bundle, GEN, and the other retained generators are excluded exactly as in the fixed-builder proof.

It remains to inspect an arbitrary H minor at parameters x,y,z. Matching always gives

`c=I(z,U_minor(x,y,z))`, `x=W_u(b,c)>c`,

`a=I(I(x,z),I(y,z))`.

If the minor's orientation contains its first parameter x, then `U_minor(x,y,z)>x`, so

`c=I(z,U_minor(x,y,z))>=U_minor(x,y,z)>x>c`,

a contradiction. This is the missing cross-orientation case not covered by simply reusing the fixed-builder statement.

If the minor is H_t using W_t(y,z), then `c=p_t(y,z)` and `x=W_u(b,p_t(y,z))`. Its output is exactly D_tu(y,z,b), one of the four admitted mixed families.

## 3. No J or mixed D major fires

For a J_t(b,c) major the required minor is `I(p_t(b,c),c)`. The fixed-builder exclusions work uniformly over all orientations:

- Any H minor forces its first parameter x to equal `W_t(b,c)` and its full consequent to equal c. Hence `c>=x=W_t(b,c)>c`, regardless of that H's builder.
- Any J_u minor forces its final parameter z to equal W_t(b,c) and `c=I(y,z)>=z>c`.
- Any mixed D minor forces its I-headed p to equal W_t(b,c).
- Identity, retained rows, bundle, GEN, and monotonicity fail by the same growth/tag contradictions already recorded.

For a D_tu(b,c,d) major write p=p_t(b,c), w=W_t(b,c), h=h_tu(b,c,d). Its required minor is `I(h,p)`.

- Identity forces h=p; comparing right fields gives `I(b,c)=w`.
- Rho6 forces `1=I(b,c)`.
- Every H minor, regardless of orientation, has consequent `I(I(x,z),I(y,z))`; equality with p forces `I(y,z)=w`.
- Any J_v(y,z) minor first forces y=c,z=w from its consequent, then z=I(b,c) from its antecedent.
- Any D_vw minor forces its I-headed p_v to equal w.
- Bundle has consequent 1 rather than I-headed p. The other cases fail by antecedent or outer tags.

Every displayed collision is impossible. These exclusions do not depend on t=u, so all four mixed D families are inert as majors.

## 4. Closure and exact scope

Induction on an S major witness now proves MP closure exactly as in the fixed-builder proof: first-parameter H majors produce identities or cannot fire; last-parameter H majors produce a J or mixed D; J/D majors cannot fire; retained rows, GEN, identities, and quantified monotonicity use their unchanged cases.

S contains truth through `I(0,0)=0`, all six row families, and every actual full bundle. All its members have residue 0 or 2, so F=1 is absent. Embedding finite derivations into S proves consistency. The positive p_t values and numerical constructor injectivity handle all zero aliases.

This strengthens the published separate-orientation obstruction and rules out any subunion of these six schemes. It does not cover added K/S, a differently shaped implication-headed fourth builder, a raw Cantor pairing code, dominated-U families, or other arithmetic code functions. It claims no source-size or machine-state bound.
