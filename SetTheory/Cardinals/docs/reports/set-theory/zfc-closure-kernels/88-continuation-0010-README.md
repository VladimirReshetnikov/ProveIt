# Independent audits

These standard-library Python programs independently parse the frozen literal
source and emitted artifacts. They do not import the searcher, optimizer, or
the delivered symbolic binary runtime checker. Their scope is recorded in each
JSON result. The exact source parser and consumed-path control arithmetic are
shared in `independent_cfg.py`.

Run from the package root. Quotient, fixture, and affine audits have complete
portable defaults:

```sh
python code/audit/check_root_quotient.py
python code/audit/check_quotient_fixtures.py
python code/audit/check_affine_certificates.py
python code/audit/check_increment_incidence.py --output results/audit/increment_incidence_audit.json
```

Candidate checks take explicit graph or table paths. `check_commutation.py`
checks the exact 242-region CI7/transfer commutation against the literal source.
`check_candidate_graph.py` checks an exact occurrence-CFG correspondence to the
literal source. `check_reassociated_graph.py REFERENCE CANDIDATE --output FILE`
checks the same correspondence between two emitted source DAGs. The latter is
used to compose the commutation proof with subsequent reassociations.

The explicit `--operational-controls` option permits a CB/CC instruction or
operand to change only when the newly parsed resolved successor still matches.
CI/CD operands, halt, every guarded edge, and initial control must agree. The
result records literal-label equality separately from operational-label equality
and lists all changed controls. This mode is used for the s10 control-readdressing
experiment, whose blank initialization remains unresolved.

`check_candidate_boot.py TABLE --output FILE` independently replays all 410,735
blank-tape transitions and compares the entire resulting tape to an explicitly
generated frame. Use `--allow-changed-prefix-rows` for the commutation derivatives:
their two edited q106 rows occur during the prefix, while the full final frame
remains identical. This option does not weaken the exact frame check; it permits
the separately recorded changed-row list to be nonempty.

The original interval certificate, affine candidates, quotient certificates,
finite fixture inputs, and increment incidence matrix are copied verbatim into
`experiments/audit_inputs/`. Default results are under `results/audit/`.

These are ordinary finite and induction certificate checks, not proof-assistant
endpoints. Finite fixture validation is not a universal binary simulation proof.
The scoped incidence rigidity theorem is not a lower bound on Turing-machine
states. See the report and proof includes for the precise theorems.
