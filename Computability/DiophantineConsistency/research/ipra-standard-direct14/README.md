# Standard iPRA for the direct-square fourteen-variable equation

The historical AQ29 parent already contains the direct-square literal and
native endpoint for the 14-variable, degree-30, 90-operation candidate
displayed in `../../equation30-direct.pdf`. Its independently audited author
and peer states both record exit zero and matching source/object hashes for
`AdaptiveSquareWitnessDirect14` and `IPRASquareWitnessDirect14Native`. Their
parent rows did not themselves print axiom diagnostics: the separate native
check module was not in that parent snapshot.

The recorded [`survey.py`](survey.py) run follows the declared project
imports of the native endpoint in the authenticated parent manifest. It
finds 1,099 parent modules, no missing workspace sources and 15 workspace
source-byte drifts, listed individually in [survey-receipt.json](survey-receipt.json).
This is a point-in-time declared-source survey, not a current-source build or
complete dynamic/package dependency trace.

The new `IPRAStandardDirect14` client transports the native equivalence to
the same-language standard theory and proves its equivalence to the selected
Foundation ZFC consistency sentence under the recorded embedding and
Gödel–Gentzen translation. It requests five native theorem axiom reports and
three standard endpoint reports. An exploratory run rebuilt the four
standard-theory extension modules plus this client in a single fresh overlay
over the audited AQ29 author parent. All five module exits and the outer
process exit were zero; all eight selected reports listed only `propext`,
`Classical.choice` and `Quot.sound`. These are Lean metatheory axioms, not
additional axioms of the object theory. The standard-theory log contains
unused-simp-argument warnings. The exact logs and observation are under
[`exploratory/`](exploratory/terminal-observation.json).

The exploratory overlay was `/tmp/ipra-standard-direct14-exploratory-20261101`,
whose project files were linked only to the audited AQ29 author provider;
new extension objects were compiled there. It did not guard all inputs before
and after the run and does not establish a guarded or paired extension, a
current-source result, formal PDF semantics, or an identification of the
translated formula with untranslated Con(ZFC). The displayed fixed decoder
and rank recipe retain the manual-transcription boundary, and the parent
package-transitive, dynamic, between-observation and Foundation-wrapper-exit
limitations remain.

`build_manifest.py` takes a committed source SHA and freezes exactly the four
standard-theory additions and this client for the existing guarded
author-only runner. It records the eight diagnostics explicitly. The guarded
run must compile all five in a fresh overlay over the AQ29 parent; it must not
reuse the exploratory outputs. A successful author run and a later matched
peer and independent artifact audit remain distinct results.

The frozen source commit is `777716daef4825d6b3023446b457f12d83aca67f`.
The resulting manifest SHA-256 is
`d2ff86b187c8b4aeb97dc701bfc7ba33b050b38c873cc5ceb6fb174991744690`;
the guarded runner's source validation exited zero for all five additions
and eight diagnostics. The first manifest-builder attempt failed on a
mistyped parent-manifest hash before writing output; the corrected attempt
and its observed exit are recorded in `manifest-observation.json`.
