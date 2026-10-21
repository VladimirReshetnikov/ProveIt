# Why the shared state164 MP shortcut changes the logical calculus

The tempting row edit `164/1 : 1 R 98 -> 1 R 114` bypasses the PUSH19 part of the shared PUSH19;COPY7 macro. At the MP-success use, omitting the push of truth0 has a valid existing compiler repair. In the accepted K215 table, however, state164 also enters four AX occurrences. The deleted pushes are at the starts of the rho6, rho4, rho2 and rho1 constructor words, respectively source intervals [888,907), [1467,1486), [2062,2081), [2412,2431).

A copy macro adds its parameter to the current register; the skipped PUSH normally saves and clears that register. Consequently these four omissions do not merely remove stack entries. They add the completed preceding formula code to the first binder of the next row.

Writing G for growG, and rho3/rho5 for the accepted rows, the changed intermediate formulas are

    r6*(A,B,C) = Ex_(A+G(A,B,C))(Q_A C) -> C,
    r4*(A,B,C) = Q_(A+rho5(A,B,C))(Q_B C) -> Q_B(Q_A C),
    r2*(A,B,C) = Q_(A+rho3(A,B,C))(B->C) -> (Q_A B -> Q_A C),
    r1*(A,B,C) = Ex_(A+r2*(A,B,C)) E(A,B).

The final AX stack is

    [r1*, r4*, r6*, rho8, GEN, old_current] old_stack.

The original G, rho5, rho3 and rho2 outputs are no longer independent stack entries. Their codes occur inside arithmetic binder indices, and r2* is itself consumed while forming r1*. The unchanged final bundle remains current under its original gate. This diagnosis is independently corroborated by the machine agent's literal macro interpretation in `research/machine/omit164_symbols.py` and `.txt`.

The changed rows are not obtained by a consistent permutation of each original row's parameters. For example the old rho6 repeats the same index A in Ex_A and Q_A; r6* has different indices unless G=0. Therefore the simple axiom-family proof for rho6(A,B) does not apply. Native arbitrary-code soundness does not declare these mixed-index formulas theorems. The lost equality/substitution rows also remove premises of the inherited calibration.

Every added formula code is a multiple of4, so the shifted binders are congruent to A modulo4. Interpreting all indices only modulo4 does not immediately repair the construction: the unchanged gate tests literal inequalities C!=A,B, which do not imply inequalities of residues, and the bundle relies on its literal private-label discipline. No consistency transport or alternate variable model is supplied by this congruence observation.

This is an exact source-level diagnostic, not a proof that every such weakened calculus is incapable of ZFC calibration, and not a bounded search asserted as a lower bound. No new binary machine with the required equivalence follows from this shortcut. Recovering soundness and consistency strength for the displayed new calculus is a separate unsolved problem.
