REJECTED PARITY DELETION: AN EXACT FALSE-GOAL CERTIFICATE

This directory is negative evidence. REJECTED_UNSOUND_no_parity.py is
deliberately unsound and must never be used as an arithmetic proof checker.

The original whole-JSON computation-leaf checker is the current 473-byte
program from ipra_vacuous_specialization. The experiment deletes exactly
the factor d % 2 from its opener's fallback. The resulting program accepts
a canonical closed guarded formula which is false in the natural numbers.
The original rejects the same certificate. Both results hold with and
without Python optimization (-O).

Reproduce:
    python3 verify_parity.py

THE FALSE FORMULA

    A = D_{x,y}( I(y,0;u.0) = I(y,0;u.S(0)) ).

By the ordinary reading, this is
    exists x ( E(x,0) -> forall y E(x,y) ).
The variable x is unused. E(x,0) is 0=0, while E(x,1) is 0=1.
Therefore A is false in the standard natural numbers. It meets the public
guard exactly: both iterator counters are y and both initializers are 0.
Its compact encoding is A=[E], E=[[5,0,0],[5,0,[0]]]. The label 5 is the
canonical y slot below the iterator's dummy counter slot.

THE COMPLETE CERTIFICATE

Let B=[A,A,A] and M=[B,A]. The JSON stack, consumed from right to left, is

    [ [[],0,[],0],
      [[A],0,0,0],
      [[],E,A,A],
      [M,B,A,0],
      [A,0] ].

Here A, B, E and M are textual abbreviations expanded in false_guarded_goal.json.
Every actual JSON node is an exact integer or a list. No Boolean, floating
point number, object or other out-of-contract datum is used.

MECHANISM

The opener normally uses depth parity to distinguish a term position from
a formula position. Removing parity lets the scalar template 0 act as an
identity template on formulas at a formula root, while it still denotes
the number zero at a numerical root.

As formulas, B is Q applied to A with an unused newly bound variable.
It is therefore the vacuous closure A -> forall z A. The certificate
derives B by opening D applied to A; that introduction uses its assumption.

As numerical raw trees, E has arity two and denotes zero, A=[E] denotes
successor of zero, and B=[A,A,A] denotes I(1,1;u.1). The equation M=[B,A]
is accepted by the computation leaf [[],E,A,A]. This numerical computation
is legitimate under the inherited raw-tree interpretation.

The outer packet [M,B,A,0] uses the illicit scalar formula template to turn
that numerical equality into replacement of the goal A by the formula B.
The resulting accepted public conclusion is false. The original parity
factor prevents exactly this crossing of numerical and formula meanings.

ATTRIBUTION AND LIMITS

The necessity of sort parity, the false guarded formula, and the original
attack were already recorded in the repository's validated_core package
and the article subsection 'A rejected saving'. The present contribution
only adapts that attack to the newer computation-leaf, whole-JSON,
473-byte protocol. The original attack's scalar template 100 fails during
the newer eager computation probe; scalar template 0 makes the attack
work in this protocol. No new mathematical obstruction is claimed.

PROVENANCE.json pins the repository commit, archive/member identity and
original counterexample. prior_parity_guard_original.json preserves the
attributed old fixture. verification.json records the four actual process
outcomes and exact source measurements. The supplied Python programs are
not new Lean or Rocq formalizations. Finite tests of one input establish
this counterexample, not universal correctness of the original checker.
