Decoder searches: reproducible inputs and explicit limits
=========================================================

These optional experiments explore source-tree reassociation, literal
reader allocation, and compatible finite-history folds. They are not
needed to rebuild or verify PA194J or PA194D.

searches.json records each completed run's source, input, attributes,
random seed, time budget, mutation count, best score, and evidence scope.
The matching .log and .csv files are retained. The C++ programs use only
the standard library; screen.cpp is their shared evaluator.

Example: the run that discovered PA194D
--------------------------------------
From this directory, compile to a writable executable location:

  c++ -O3 -std=c++17 search_closing_adaptive.cpp -o /tmp/pa194_search
  /tmp/pa194_search separateD.txt closing_attrs.txt /tmp/separateD 240 202611140764

The prefix argument controls output filenames. Avoid overwriting the
frozen evidence. Wall-time stopping makes the number of mutations depend
on the host. A deterministic seed does not promise identical final output
after an equal wall-time budget. The winning grammar is frozen separately
in ../../logical_emitter/inputs/winner.grammar.json from this directory,
or, relative to the archive root:

  logical_emitter/inputs/winner.grammar.json

The frozen witness and its construction verifier, rather than successful
rediscovery in a time-limited search, reproduce the mathematical result.

How to read the score
---------------------
The base score is raw AX readers minus a jointly compatible set of folds.
Scanner/address violations add penalties. The fixed controller has 134
controls in these runs. A zero-penalty score 60 is an allocation candidate
for 194 states; score 59 would be a candidate for 193. Neither score proves
legal source control flow, exact startup, a universal physical simulation,
or the required logical calibration. Those are separate acceptance gates.

The programs screen history folds for simultaneous compatibility. This is
stronger than simply adding the sizes of independent fold opportunities.
Nevertheless, the accepted witnesses are also checked by complete local
traces on the final quotient and by the independent whole interpreter.

Run families
-------------
CSZ/CZ combine published cached or symmetric controllers with the X-zero
scheduler jump. Suffix103A/103X changes the other known-zero return reader.
closing103A also changes the final AX return among candidate zero tests.
negation_search mixes alternate 18-site/47-site negation spellings.
h1D explores a 191-token logical-head transfer.
separateD/separateH use the 190-token Gamma(D)/Gamma(H) emitter.
The adaptive versions retain candidate pools within two points of the
current best score, allowing searches that begin above the old threshold.
warm_D_CSZ_A/X restart from the successful Gamma(D) grammar and its pool
under the additional J-family helper interfaces.

All fourteen runs ended without a score below60. Only the successful
separate-D witness was promoted to a new logical 194-state construction.
The other best grammars are search artifacts, not accepted machines.
Failure of these finite searches gives no lower bound or global optimum.

Provenance
-----------
screen.cpp and occurrence-search structure are adapted from the supplied
ProveIt incoming pa194C_conpa_2026-11-13 (2).zip, search/grammar/.
Task-specific changes include new controller input tables, logical emitter
seeds, known-zero decrement leaves, and adaptive candidate-pool admission.
See the root NOTICE.txt and preserved ProveIt/upstream license notices.
