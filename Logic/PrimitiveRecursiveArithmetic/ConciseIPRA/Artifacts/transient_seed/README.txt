A ONE-STATE RECURSOR FOR iPRA
Prepared for Vladimir Reshetnikov, 10 November 2026.

Read report.pdf or compile report.tex with python3 build.py.
All LaTeX inputs are under theory/ and evidence/.
Run python3 verify.py to reproduce source measurements and finite evidence.
Python 3.12.14 was used for the recorded source metrics.

Main mathematical results
-------------------------
The one-state successor-seeded recursor
  R(0,a;h)=S a; R(Sn,a;h)=h(R(n,a;h)), with S a := R(0,a;0),
recovers arbitrary initialization. Transient seeds supply selected zero-start
orbits, a factor-map comparator, and a reset-cycle predecessor satisfying
P(0)=0 and P(Sa)=a. Every induction is on a literal equation with passive
parameters fixed. The initialized iterator is then
  I(n,a;h) = P(R(n,a;v.S(h(P(v))))).

The native logical bootstrap is also closed: a finite decoder cancels S on
Boolean values before a general predecessor is available. Restricted native
implication then supplies contextual Boolean equation cases, enough to carry
the arithmetic proof in the small Choice-DI logic. Full intuitionistic logic
is reconstructed only after predecessor yields an unshifted selector.
The direct native SR theory is whole-domain bi-interpretable and equiconsistent
with iPRA, including native-formula return translations and identity numerical
composites. The complete report states every primitive rule explicitly.

A separate tied-seed recursor cannot represent addition, general selection,
or injective pairing by terms: each of its terms has a single bounding input
coordinate. This does not exclude every relational or domain-changing
interpretation.

Measured comparison and exact limits
------------------------------------
Current corpus envelope: 281 tokens / 315 AST nodes / 685 normalized bytes.
Direct native SR checker:284 tokens / 322 AST nodes / 681 normalized bytes.
Auxiliary I byte profile:282 tokens / 320 AST nodes / 679 normalized bytes.
Auxiliary I structure:   280 tokens / 311 AST nodes / 705 normalized bytes.
Auxiliary I joint:       280 tokens / 314 AST nodes / 684 normalized bytes.
The direct new arithmetic checker beats the supplied byte frontier. Distinct
auxiliary programs attain the new coordinate minima. The I joint profile
is a single complete program strictly below all three OLD coordinate minima;
no single program attains the whole new envelope. All complete source is charged under the unchanged
corpus metric, including input, validation, and ACCEPT/REJECT output.

The proofs are written internal arguments, not Lean/Rocq formalizations.
Finite tests check transcriptions and actual primitive proof certificates.
No absolute minimality or literature-wide priority claim is made.

The source review is pinned to ProveIt commit
2fdcf5bf988bead821c416649f713f98b7ed8776, docs/drafts.
All nine archive identities, direct source metrics, and nested historical
reference metrics are recorded in evidence/. Frozen incumbent programs
and their unchanged source normalizer are under reference/.

Checker use
-----------
python3 code/checker_sr_bytes.py < certificate.json
python3 code/checker_bytes.py < initialized_I_certificate.json
python3 code/checker_structure.py < initialized_I_certificate.json
python3 code/checker_joint.py < predecessor_packet_I_certificate.json

Certificates are JSON arrays of commands followed by their native goal.
Input is never executed as Python code. The SR program checks successor-seeded
recursion; the auxiliary profiles check initialized I. The joint profile has a changed
predecessor-packet format, documented and proved complete in the report. Their computation
schemas and source metrics must not be conflated.

Reproducibility and attribution
------------------------------
The small checkers derive from ipra_generated_assumptions_2026-11-10.zip.
The factor-map strategy and arithmetic completion are attributed to the
supplied scalar development. Transient initialization, the reset-cycle
predecessor, the native finite-Boolean bootstrap, and the tied-seed bound
are new relative to the inspected drafts. See the report for full definitions,
proofs, both interpretation composites, and further research questions.

DIRECT NATIVE SR CERTIFICATES
-----------------------------
examples/boolean_decoder.json is a 45-command native proof of the finite
Boolean decoder closure. examples/restricted_boolean_implication.json has
149 commands and genuinely uses its retained Boolean antecedent. The
aggregate tests/sr_certificates.json contains 26 direct SR cases. Rebuild
them with python3 tests/sr_producer.py. The new I predecessor packets are
reproducible with python3 tests/joint_producer.py. Both producers are
untrusted; no small checker imports a producer or evaluator.

AXIOMS.txt is a compact standalone inventory of the complete native SR core.
