# Independent review: cleared current14 integer syntax and iPRA

**PASS within captured-provider scope.** The checked
[`ClearedCurrentIPRA.lean`](../../research/rational-carrier64-cleared-ipra/ClearedCurrentIPRA.lean)
defines `clearedExpression` to be exactly the existing integer
`expressionAt CurrentWindowCarry2011.ports`. The theorem `cleared_eval`
uses the previously checked current-base binding to identify its evaluation
with the 65-row `value65` at that same actual port tuple and valuation.
`clearedNoZero` applies the same positive shift and split-natural encoding as
`noZero14`; `clearedNoZero_eq_noZero14` is checked by definitional equality
`rfl`. The final theorem rewrites this identity and uses the second conjunct
of the checked pair to obtain the existing standard-iPRA derivability
against the intuitionistic negation of mapped native refutation.

The word “cleared” is the client's name for the already existing 65-row
integer syntax. The prior external rational evaluation theorem supplies the
ordinary rational/integer connection; this file does not formalize a
rational-expression clearing algorithm, introduce a rational object-language
term, prove an internal rational-leaf equivalence, or establish a 64-operation
integer equation. It does not assert a zero or Con(ZFC).

Attempt01's retained log/result match their temporary originals, record Lean
exit 0, no stop and the three expected axiom reports. A separate retained
outer observation records session 52395 exit 0; this review did not observe
that earlier session directly. The output object, four explicitly guarded
provider objects, pair and 65-row binding receipts, pair outer observation
and fresh-base state match their pins. Independent [check.py](check.py)
ran exit 0 and rechecked all 186 recorded direct/companion/shadow guards,
the predecessor terminal states and sampled resource receipt;
[result.json](result.json) records the outcome. No Lean replay or complete
transitive/dynamic ancestry audit was run; prior fresh-base provenance and
sampled monitoring limits remain inherited.

Checker SHA-256
`965906e87dc541aac649cd89914efb6a91c2bb3f2c66921aee0dfb50a9efd1c7`;
result SHA-256
`e503598bc6c90eda96eb42a3f720b60f70eb80ba838d1a69f8dc85da8872b6e4`.
