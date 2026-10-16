# Final engineering result: original-rho6 candidate in 248 states

The recommended candidate is now the **248-working-state original-rho6
machine** in `reproduced-248/raw-candidate-old_rho6-248.tm`. It has 186
decision states, 62 framework states, exactly 496 transitions, start state 0,
and terminal target 248. The SHA-256 is
`e9cf9241e0012c56ecf4dc55f969d4c01e988a5c3839c9e4a49b5fae33591d45`.

This is an equality-free raw candidate, **not yet a proved ZFC-consistency
machine**. Its advantage over the previous raw 252-state artifact is that
it is smaller while retaining the original quantifier axiom. There is no
remaining reason to prefer the dual quantifier change on state-count grounds.

## Attribution and exact change

The supplied incoming `zfc_one_schema_research` report already introduced
the weighted Re-Pair grammar method and applied it to the published 219-node
AX program, obtaining 207 decision nodes and a 269-state complete Wade
machine. Its `machine/rebracket_axioms.py` has SHA-256
`bdbf5a84ab1a2914e351e917d7ff3994fec5729bddbe33971678cd51c2839119`.
That algorithm and its certificate architecture are prior work, not a new
discovery in this research session.

The new experiment applies that exact method to the new parameter-permuted,
base-3, equality-free AX word described in `TM_ENGINEERING.md`. It retains
the same complete interpreter and the same literal register-helper bodies.
The only helper difference from the original published program is the
already selected formula scaler from four increments to three. No new
logical axiom rewrite is introduced by rebracketing.

The AX word has 138 macro calls. Each macro is checked to be closed with
respect to its internal break/continue operations. Re-Pair replaces repeated
adjacent token pairs by shared binary productions. This changes the binary
decoder grammar while preserving the expanded macro word.

The bounded experiment tested exactly 1,025 seed/exponent choices for each
of the two words: the incoming report's seed 341 and exponent 4, then seeds
0 through 255 at exponents 1, 2, 4 and 8. It took about six seconds for both
searches. The minimum in both finite searches was 248 states. No global
minimality is claimed.

| Candidate | Source full count | New decision | Framework | New full count | Seed | Exponent |
|---|---:|---:|---:|---:|---:|---:|
| Original rho6 | 252 | 186 | 62 | **248** | 122 | 2 |
| Dual rho6 | 250 | 186 | 62 | **248** | 39 | 2 |

The original-rho6 winner has 22 new grammar productions and a residual
word of length 63. The dual winner has 23 productions and a residual word
of length 62. The supplied generator uses these fixed seeds and does not
rerun the search.

## Exact RM-equivalence certificate

For each variant, the generator emits the source candidate's RM DAG, the
rebracketed RM DAG, and a finite relation between their instruction sites.
Both relations contain 3,394 pairs: 1,491 decrement-test pairs, 1,902
increment pairs and one halting pair. Both zero and positive successors of
every decrement are checked. The initial program counters are related and
all certificate pairs are reachable in the conservative operation graph.

For original rho6, the reference decoder has 190 nodes and the candidate
186. Both unfold to 4,881 instruction sites. Maximum path lengths are 79
and 83 respectively; the maximum contracted control-only path is four steps
in either program. The dual reference has 188 nodes and maximum path length
78, with a candidate maximum of 82.

**Certificate theorem.** Suppose two register-machine programs have a finite
relation between operation sites containing their initial sites. Suppose
related sites carry identical increment, decrement-test or halt operations,
and each corresponding successor operation site is again related after
finitely many control-only transitions. Then the two programs have identical
halting behavior from every common initial register vector.

**Proof.** At related sites, identical register vectors determine the same
decrement branch and receive the same register update. The successor
condition restores the relation after finitely many register-preserving
control steps. Induction gives correspondence at every operation boundary.
If one run halts after finitely many operations, the other reaches the
related halt site after the same number of operations and finitely many
additional control steps. The reverse direction is symmetric. No assertion
about a mathematical theory is needed. End of proof.

The finite certificates were checked by a second implementation using the
incoming report's independent string/integer path engine from
`verify_rm_certificate.py`, SHA-256
`30fbd95b7a2a61004422558cfab4419de5239b67b88bc9ed19b7de8fcf585f18`.
Our small `verify_schema_rm_certificate.py` wrapper generalizes that
verifier's fixed 219-node source input to the explicitly supplied 188/190-node
reference DAGs. It does not import the grammar generator or TM compiler.
Both certificates pass. These are executable finite certificates, not a
Lean/Rocq kernel verification and not a proof of the binary TM compiler.

The generator also re-extracts every emitted decision transition back to
its RM edge, including the bit-dependent break/continue conventions. This
finite correspondence check is separate from the still-required theorem
that the complete binary interpreter realizes RM semantics.

## Reproduction

```
python generate_schema_candidates.py \
  --repo /path/to/ProveIt \
  --rebracket-dir /path/to/zfc_one_schema_research/machine \
  --output /tmp/schema-248
```

Use ProveIt commit `17d0f2eaa650901cda59764dfcc4661c199e49c8`. The generator
checks source hashes before executing the existing research helpers,
the incoming rebracketing code and the MIT-0 Wade backend. It produces both
248-state tables, named tables, label maps, reference and candidate DAGs,
RM certificates and source metadata. A second invocation reproduced the
search's exact total tables byte-for-byte.

To verify the original-rho6 RM certificate independently:

```
python verify_schema_rm_certificate.py \
  --prior-machine-dir /path/to/zfc_one_schema_research/machine \
  --reference /tmp/schema-248/old_rho6-reference-dag.json \
  --candidate /tmp/schema-248/old_rho6-dag.json \
  --certificate /tmp/schema-248/old_rho6-rm-bisimulation.json
```

| Final file | SHA-256 |
|---|---|
| Original-rho6 named source | `51ad9b18f5933d51b27bb274bfefafdb0f02e0616541442f2966ca71805eeb7a` |
| Original-rho6 total table | `e9cf9241e0012c56ecf4dc55f969d4c01e988a5c3839c9e4a49b5fae33591d45` |
| Dual-rho6 named source | `d88e75ee1859734a10bfe819f92fbd7cce1ff9ff3425b364bf90e986cb823dea` |
| Dual-rho6 total table | `70d141e1a2872a3080b525a4061b48882131e636c41444f09bc065647a7e4a6c` |

## Table audit and remaining gap

The independent auditor finds all 248 working states graph reachable, 248
singleton exact step-bisimulation classes after 11 refinement rounds, no
startup-state reuse and no safe state merger within radius 4 and 64 local
steps. For original rho6 it checks 24,092 abstract configurations and 61,256
ordered state pairs, admitting all 496 rows. The dual case checks 24,316
configurations and the same number of ordered pairs.

Both one-million-step blank prefixes match the earlier raw candidates:
state 24, head 248, 223 one-cells. They do not reach AX. They give no evidence
for nonhalting and do not validate the edited theory routine.

The precise remaining work is the equality-free comparison-theory/calculus
calibration, the base-3 codec and enumeration adequacy, and complete binary
interpreter simulation. The new parameter permutation is an exact bijection
of axiom instances, and the grammar change has a finite RM-equivalence
certificate. Thus these two new compiler reductions can be verified
independently of the unresolved set-theory question.
