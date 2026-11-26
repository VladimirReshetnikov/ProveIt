# Lean formalization plan

This is a mathematical implementation plan, not compiled Lean code.
The package contains no file that pretends the new theorems have already
been kernel checked. The upstream project pins Lean 4.35.0 and Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679.

## A. Finite shell layer

Represent the primitive p^h roots by units of ZMod (p^h), with multiplicities
of marked leaves represented as a finite multiset.

1. cyclotomic_distance: for distinct units a,b modulo p^h, prove the
   normalized valuation of xi^a - xi^b is r_(h-vp(a-b)).
2. least_occupied_branch: a multiset of m marks in a residue tree has
   a leaf whose depth-j ancestor contains at most floor(m/e_j) marks.
3. nearest_torsion_projection: replacing an arbitrary shell root by a
   nearest torsion point weakly increases its potential at every leaf.
4. shell_minimum_le: deduce U_h(m) for m < e_h.
5. balanced_marks_attain: the first m unit representatives attain U_h(m).
6. critical_floor_identity: prove

       e_h * U_h(M_h-1) = (h-h0) M_h - (p^(h-h0)-1).

All floor statements can first be implemented over natural numbers. The
code directory contains exact computational examples, but they do not
substitute for these quantified lemmas.

## B. Polynomial layer

Use the factorization of a nonzero polynomial over an algebraically closed
valued field and multiplicativity of weighted Gauss valuations.

1. gauss_of_roots: G_u(g)=v(b)+sum min(u,v(alpha)).
2. selected_shell_budget: Delta_rho(g) bounds sum m_h/e_h.
3. old_shell_slack: G_rho(g)-G_r_h(g) bounds the exact weighted earlier
   shell counts.
4. blocking_forces_root_count: inductively m_h >= (p-1)p^(h-h0).
5. blocking_budget: N blocked shells force Delta >= N p^(1-h0).
6. exact_selector: derive H=h0+floor(B p^(h0-1)), including equality cases.
7. sharp_obstruction: build the balanced polynomial and prove strict
   failure at all endpoints.

Keep v(0)=infinity separate from real finite Gauss values. In the proof
with m<e_h, the chosen leaf avoids projected roots; its potential is finite.

## C. Analytic and packet layer

1. Prove a coordinate-substitution lemma using a coefficient attaining G_rho.
2. Keep a real lower coefficient bound a=inf v(a_n); do not attempt to
   choose a scalar of valuation a.
3. Prove uniform tail control on the finite torsion grid.
4. Apply to bounded series via total-degree truncation.
5. Prove packet selection by Gauss multiplicativity of a finite product.
6. Prove the G_0 identity by taking positive-radius Gauss limits if needed.

The target inequality is aggregate. A theorem asserting exact bounds for
each factor would be false. The coordinate orders are independently chosen
from a common interval.

## D. Lubin–Tate layer

Abstract the shell tree first, with branch sizes q-1,q,q,... and distances
r_h=1/((q-1)q^(h-1)). Instantiate it using the standard rank-one torsion module,
primitive Newton-polygon radii, and the unit factor relating ordinary and
formal differences. Normalize the valuation by w(pi)=1.

## E. Artin detector layer

The exact finite group work is separate from analytic number theory.

1. Verify the A5 character table and subgroup inductions.
2. Prove 4 chi^4 = Reg + 11*1 + 9*Ind_D5(epsilon)
   + 12*Ind_C5(lambda) + 11*Ind_A4(omega).
3. Prove the restriction properties of Theta=-chi+chi'+eta.
4. Deduce the sharp order cone inequalities.

An analytic formalization additionally needs Artin meromorphic continuation,
Artin induction/restriction, Hecke holomorphy/nonvanishing, and the residue
calculation. They are not supplied merely by finite character arithmetic.

## F. Where upstream reuse needs care

The source lemma
New.Selmer.exists_rootsOfUnity_ellVal_eval_le_add supplies individual
positive-tolerance inequalities. The new exact aggregate selector is not
a drop-in replacement at every call site.

The source general Selmer theorem assumes finite congruence terms.
Changing the selector does not discharge that assumption.

No global A5 prime-sum square-root bound has been formalized or proved in
this package.

