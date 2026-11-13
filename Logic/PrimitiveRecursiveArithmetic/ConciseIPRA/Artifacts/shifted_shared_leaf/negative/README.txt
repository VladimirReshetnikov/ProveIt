Parity-deletion counterexample for the shifted shared-leaf checker
================================================================

This directory is negative evidence. The program whose name contains
"no_parity" is a deliberately unsound diagnostic program; it is not a
candidate arithmetic proof checker.

The diagnostic deletes exactly "d % 2 *" from the opener fallback of the
468-byte checker. The resulting checker accepts the false canonical closed
guarded formula

    A = D_{x,y}( I(y,0;u.0) = I(y,0;u.S(0)) ).

The bound variable x is unused. Its matrix E has value 0=0 at y=0 and 0=1
at y=1. Thus the ordinary conditional-closure reading of A is false in the
standard natural numbers. Both iterator terms have the public guarded
shape, with counter y and initializer 0.

Let

    E = [[7,0,0],[7,0,[0]]],  A=[E],  B=[A,A,A],  M=[B,A].

The complete certificate, with these abbreviations expanded, is the stack

    [ [0,0,0,0],
      [0,0,0,0],
      [0,0,0,0],
      [0,0,[],0],
      [[A],0,0,0],
      [0,E,A,A],
      [M,B,A,2],
      [A,0] ].

It is consumed from right to left. There are seven instruction packets and
one terminal goal/floor pair. Every JSON node is an exact integer or list.

Why the attack works
--------------------
The formula-root depth is 2 and the term-root depth is 5. Scalar 2 is outside
the retained interval at a formula root, while it denotes the number zero
at a term root. After deleting the parity factor, using that scalar as a
formula template illicitly substitutes a numerical raw tree for an entire
formula. This permits an equation between the numerical readings of B and
A to turn the formula goal A into its provable vacuous closure B.

As a formula B is Q applied to A with a vacuous variable. The certificate
derives this vacuous closure by opening D applied to A. As numerical raw
trees, E has arity two and denotes zero, A=[E] denotes its successor, and
B=[A,A,A] denotes I(1,1;u.1). The equation M=[B,A] is consequently a valid
computation leaf. The unsound step is the crossing between those numerical
and formula readings, which the original parity factor forbids.

The three leading harmless packets are the added hypothesis returns of the
shared-leaf protocol. They are derived by tracing the successful run of the
shifted direct-leaf mutant, not by trusting a conjectured packet order.

Actual verification
-------------------
../verify_negative.py replays the adapted certificate against the correct
checker and the saved mutant, performing four process executions.
The 468-byte checker rejects and the mutant accepts, both normally and under
Python -O. The exact results are in ../evidence/parity_attack.json. This is a verified
counterexample to that mutation, not a proof of the unmutated checker.

Attribution
-----------
The false guarded formula, the sort-parity obstruction, and the four-packet
direct-leaf attack are inherited from the repository snapshot
78edba03ee060644464f76e388578584b356520a, at

Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/incoming/
ipra_whole_json_refinement_2026-11-12.zip

archive directory ipra_whole_json_refinement_2026-11-12/negative/.
That package in turn attributes the earlier attack to
Artifacts/validated_core/tests/parity_guard_original.json.

The present adaptation changes the bound coordinate from 5 to 7, changes
the illicit scalar formula template from 0 to 2, uses scalar neutral majors,
and inserts shared-leaf hypothesis packets. No new impossibility theorem is
claimed.

See ../verify_negative.py for the portable replay in this archive.
