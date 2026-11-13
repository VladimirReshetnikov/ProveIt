# Review of entry reservation and phase selection

Reviewed concrete files: `agent_kernel/entry_reservation.py`, `entry_reservation_plainleaf.py`, and `checker_tokens303.py`, on 2026-11-13. This is a mathematical review, not a formal verification of Python semantics.

## Entry reservation looks sound, subject to the correct native rule selector

The proposed ordering is:

1. At entry floor kappa, completely scan the goal, with public syntax validation exactly when kappa=0.
2. Decrease the global floor to alpha=kappa-1.
3. Inspect the computation candidate and packet, including any replacement and witness opening, at alpha.
4. For a nonterminal call, form the preimage of the new hypothesis before calling the major proof.
5. Invoke the major proof at alpha. Its own goal scan happens before its own entry decrement. Its returned floor beta satisfies beta <= alpha-1.
6. Instantiate the discharge/progress parameter at beta and recurse on the continuation.

The tuple expression in the implementation evaluates its left membership operand `i(a)` before the right tuple's first element `(k := ~-k)`. The only root call has k=0 for that scan. Once that scan succeeds, k is strictly negative for every later scan and every other opening. It therefore correctly replaces an explicit one-time public-validation phase flag.

The extra name alpha admitted for the packet is an ordinary free numerical parameter. The current context and pre-scan goal do not use it at semantically active term positions, because they were closed at kappa. An arithmetic axiom, an equality major, a witness, or a source formula may mention alpha; these operations are uniform in such free parameters. Since alpha is absent from the exported pre-scan goal and undischarged context, its use does not strengthen the object theory. If desired it can be specialized to zero in the ordinary realization.

The actual discharge eigenparameter is beta, not alpha. The hypothesis preimage and any witness are formed before the major call at alpha. The major's input is scanned at alpha, so every parameter name active in these expressions is >= alpha. The major call then lowers the floor at least once. Consequently beta < alpha is fresh for the major's conclusion, the caller's context, and the caller's witness/source expressions. The post-major continuation uses a legitimately fresh parameter. Raw annotations can contain other integers, but they are semantically ignored; the existing sorted-opening lemmas are exactly the appropriate criterion here.

It is harmless that beta may be mentioned inside a terminal computation candidate in the major's proof after that terminal call has reserved beta. The eigenvariable side condition concerns undischarged assumptions and the major/conclusion formulas, not a globally unique name throughout a proof branch that has already returned. If a strict presentation demands globally separate parameter names, the internal proof can be renamed apart; the completed major formula contains no beta.

For completeness, translate a canonical proof by retaining an injective map from old allocated eigenparameters to the new returned floors. Ignore the extra reservation alpha at every call. Every nonterminal instruction still checks a major (including an administrative neutral major), so the subsequent returned floor is strictly below the floor at which the witness was opened. This leaves a fresh name for each old allocation. Canonical terms and formulas are unchanged by the extra permitted but unused names. The standard renaming/opening commutation lemma supplies the induction.

The new checker does **not** accept exactly the old raw certificate set. For example, a root witness containing parameter -1 may now be legal, since -1 is an extra free parameter and the actual discharge eigenparameter is at most -2. A capture regression must target the actual later eigenparameter, not assume that it remains -1. Public theorem-set equivalence is the appropriate claim.

## Independent flaw found in the direct-terminal composition

At review time, all three named files permitted a nonterminal introduction to retain the selector

    len(a) % 2 == u

after deleting the original conditional computation-hypothesis branch. This is not sound for the intended native iPRA calculus.

In the original native three-field protocol, a truthy `u` selects computation rather than introduction. For introduction, `u=0` gives progress only at a literal equation (even arity), while a false-valued nonnumeric marker selects cases. Thus a compound matrix cannot receive a progressive hypothesis.

In the direct-terminal rewrite, a packet whose computation candidate fails may fall through to introduction even when `u=1`. For a compound instantiated matrix of arity 1 or 3, `len(a)%2 == u` is then true. The branch uses `B(t,z)` as its hypothesis and asks for `B(t,Sz)`, introducing `D_xy B` by progress on a compound formula. This is an extra induction principle; the inherited iPRA bridge does not justify it. Standard-model truth is not a useful test, since full formula induction is true on standard natural numbers.

A repair must preserve the old dispatch precondition or explicitly choose progress only when the matrix is a literal equation and the relevant native mode has its designated numeric value. Using `not u` alone would also conflate the old case marker [] with the old progress marker 0. Entry reservation should be evaluated only after this independent rule-selection issue is fixed.

## Final correction and review

The kernel agent corrected the selected candidates. The current three-field `entry_ast.py` and four-field `entry_four_bytes.py` use the exact test `len(a) == 2 == u` for progress. Thus the new progress marker is integer 2, a compound matrix can never select progress, and [] or 0 can request cases. The fixture compiler was updated to emit those new markers. This is a specified certificate-format change, not an equivalence of arbitrary old and new raw stacks.

Both corrected files were read in full after the fix. No remaining mathematical blocker was identified. The three-field structural pattern version relies on the same CPython 3.12 sequence-pattern binding behavior already qualified in the upstream article. The four-field version forms its hypothesis preimage before the major call and performs the replacement endpoint check afterward. This latter order is safe for the inherited reason: a successful replacement has a literal major matching either the source-target pair or the triplicated Q template, and that major was scanned at the pre-reservation floor alpha. Thus active source/target/template parameters cannot secretly acquire the later fresh name beta. Ignored annotations stay ignored under the numerical reading. The intro witness was also validated before beta was reserved.

The four-field eager opener uses [] as its neutral administrative major. Its even-depth fallback still consults the missing image before multiplying by zero, so an illegal scalar public formula is rejected, even though the proof-phase reading of scalar formulas is truth. Whole-input integer/list validation remains present.
