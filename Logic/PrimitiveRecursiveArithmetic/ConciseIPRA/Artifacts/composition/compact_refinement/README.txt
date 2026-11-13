236-TOKEN DIRECT CHECKER REFINEMENT

The main checker code/checker_tokens236.py is a two-expression change of
code/control_tokens238.py under the SAME seeded-list context input contract.
Read PROOF.txt for the full universal simulation and precise limitations.
The two companion programs trade AST nodes or bytes; all three have 236
significant tokens, and none meets the full 238/255/455 incumbent envelope.
This is not a new axiomatization or a mathematical breakthrough.

Run:
  python3 verify.py

The verifier translates the inherited theorem fixtures only by changing their
first line from A to [[0],A]. All later proof packets remain unchanged.
It also checks five open-context/scope cases, runs every program in normal
and optimized Python, and checks rejection before the major-proof boundary.

Recorded result: 35 cases,280 process executions,4 boundary checks,0 failures.
An exact normalized-source scan of all 3,782 source entries at the pinned
revision found no copy of any of the three candidate modules. This is a
finite source-corpus result, not a historical-priority claim.

The frozen receipt is verification236.json. The independent duplicate audit
is source_audit236.json. Fixture provenance records the pinned Git blob SHA
for every upstream fixture. No network is needed for the functional tests.

Source baseline:
VladimirReshetnikov/ProveIt e0d702b905c74b74a23d045f8289b151bb8ebcff
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The control's source is the seeded 238-token program in
  docs/incoming/ipra_nontraditional_inputs_2026-11-13.zip
  ipra_nontraditional_inputs_2026-11-13/sequent_input/
  checker_tokens239_seeded_sequent.py
It is also copied in the incoming names_and_scopes archive.
The 30 inherited fixtures are from
  Artifacts/fused_blocks_and_checkers/checkers/fixtures/.
Upstream code and fixtures are under ProveIt's MIT-0 licence.
