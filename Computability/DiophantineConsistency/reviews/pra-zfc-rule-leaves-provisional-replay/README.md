# ZFC refutation certificate from rule-leaf bounds

`PRAWitnessCoreRules` collects witness bounds for each top-level disjunct and
its negation. Together with the separately proved formula-set core conjunct,
the positive and negative rule-leaf bounds in all candidate-PRA models imply
the actual fixed-sentence `BoundCertificate`. `PRAWitnessZFCRuleLeaves`
specializes this result to Foundation's ZFC refutation predicate.

**The rule-leaf bounds remain explicit premises.** This packet does not prove
the ZFC certificate or the equation/consistency equivalence without them.

The author run `/tmp/pra-zfc-rule-leaves-f4uaph4a` and independent same-parent
replay `/tmp/pra-zfc-rule-leaves-5hfz0sge` passed all six modules, matching
source/object/full-log hashes. Both pin 780 selected mixed-provider object
bytes and observe four current project sources. These checks do not establish
the parent objects' source correspondence, nor the inherited Foundation,
ZFCinPA, Lake fallback or package transitive ancestry. States, sources and
full logs are frozen in the adjacent evidence directories.

Replay: `python3 Computability/DiophantineConsistency/reviews/pra-zfc-rule-leaves-provisional-replay/replay.py`.
