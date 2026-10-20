# Checked conclusion: R(A,B) does not close the calibration gap

The invariant in invariant.md is now kernel-checked in DiagonalInvariant.lean.
Actual attempt4 passed in 1.794 seconds, with zero warnings and twelve axiom
probes. safe_mp, no_falsum and no_falsum_to_truth use only propext,
Classical.choice and Quot.sound. All nine native-row/bundle binding equalities
are axiom-free. No sorry or custom axiom remains.

The result is stronger than failure of a particular attempted diagonalization:

* the exact modified rows with U=R(A,B), MP, GEN and truth have no refutation;
* the auxiliary invariant freely admits every identity and quantified
  monotonicity, and remains closed under MP;
* even the literal code wim 1 0 (F implies truth, numerical code 4) is not
  derivable in the modified calculus.

Thus semantic fresh-label reasoning cannot be converted into that claimed
implication-to-truth theorem using the native rules alone. Completeness recovering native F→truth from the stated semantic validity
is false. A uniform model-existence implication strong enough to yield
Con(ZFC) cannot be proved in ZFC if ZFC is consistent. This does not exclude
the actual existence of such a semantic model when Con(ZFC) holds.

The native r1--r6 and modified r8 bindings are checked by rfl against imported
Code254. G and the bundle are checked as literal expressions. KCode222 has
no located cached object, and was not built: its growG/vrel/nks/bundle222
source definitions (lines34--51) were read and pinned separately. The exact
seed bundle is the proved general bundle at k=c and

    d = wim (clos a b c c) (wn (req b c c)).

Its complete support core is retained. In fact any Q-headed core and every
gate outcome are allowed in the proved larger system. The import boundary
is the accepted Code254 source/object pair recorded by PositiveSimulation
run4, with its existing cached namespace; no dependency is rebuilt or freshly
claimed as transitively checked here.

The displayed finite syntax proof can be formalized in ZFC by ordinary
induction. Consequently, assuming ZFC is consistent, this exact modification
cannot have a ZFC-provable implication Con(modified) -> Con(ZFC). This last
metamathematical statement uses the usual second-incompleteness theorem; it
is not a new Lean theorem about an arithmetized ZFC consistency sentence.
No candidate Turing machine is promoted, and accepted K219 is unchanged.

Adding K alone escapes this particular invariant. The additional instance
T -> (F -> T), detached with existing truth, proves F -> T, which the checked
no_falsum_to_truth theorem excludes from the old system. More generally,
K(T,B) and truth give B -> T uniformly. This says nothing yet about whether
K plus the modified rho8 recovers S, equality transport, a negative fragment,
or full ZFC strength. No such extension is asserted.

This result is stated specifically for U=R(A,B). Independent ordinary
reviews discuss related substitutions; those extensions have not been
formalized in this file. In particular it does not rule out U=R(B,C).

History: attempt1 failed because the minimal imported environment exposes
theorem rather than the lemma command; attempt2 additionally corrected
Cantor namespace qualification, unsupported placeholder shorthand and two
explicit arithmetic arguments. Attempt3 first passed the invariant. Attempt4
adds the native rfl bindings and the F->truth nonderivability result. Every
source snapshot, log and result is retained. The preliminary invariant.md
peer receipts predate the Lean check and do not claim to review its code.
