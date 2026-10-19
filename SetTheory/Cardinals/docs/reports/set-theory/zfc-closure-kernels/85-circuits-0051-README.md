# Independent source, guard, and startup certificates

All commands below run from the extracted archive root. These helpers use
Python 3 and the standard library; the optional bounded startup search
also needs a C++17 compiler. The root `verify.py` is the main positive
certificate replay and additionally checks all universal binary instruction
contracts and the inherited macro inductions.

## Independent guard transport and exact blank prefixes

```sh
python code/proof/audit_guard_transport.py --output tmp/guard-transport-independent.json
```

This command reparses the pinned original source, validates the product
invariant over all guarded source edges, checks its transport to all five
delivered programs using a separate leaf-graph implementation, and replays
the two complete blank prefixes. Its initial domain is exactly
`T=W=H=0`, with the other six logical registers arbitrary. It does not
derive that condition from the more general Safe recognizer.

The original finite merge fixtures can also be reconstructed and their
case ordering checked independently:

```sh
python code/runtime/regenerate_fixtures.py --output-dir tmp/runtime --domains unrestricted guards
python code/proof/audit_guard_transport.py --fixtures-root tmp/runtime --baseline-fixtures tmp/runtime/baseline_merges/merge-cases.txt --output tmp/guard-transport-with-fixtures.json
```

The second command reconstructs every source/expected tape and compares
every fixture row and runtime table for all six original corpora and their
six guard-only restrictions. The six excluded indices are zero-based;
decrement cases have their zero branch first and positive branch second.
The checker never reads the older generator's cached control graph.

## Complete-support startup replay

```sh
python code/proof/verify_blank.py verification/proof/lowcost
```

This independent sparse-set interpreter replays each recorded successful
blank prefix and reconstructs the entire expected infinite tape from its
finite one-cell support. It also regenerates canonical state renumberings.
The command rewrites the corresponding derived certificate files; use a
copy of that directory if preserving the byte manifest during analysis.

The recorded bounded search tried every one of the 246 working states of
each table for at most one million literal steps. It found only the two
reported roots. To repeat the full search, compile and run, for example:

```sh
mkdir -p tmp/blank
c++ -O3 -std=c++17 code/proof/search_blank.cpp -o tmp/search_blank
tmp/search_blank candidates/layout0/machine_old.tm 1000000 tmp/blank/rotation0-blank-search.jsonl
```

Run the last command with layout numbers `233`, `235`, `236`, and `237`
for the other tables. This search has a finite fuel bound. A `FUEL` result
does not establish nonhalting or rule out later initialization.

## Broader sufficient Safe certificates

```sh
mkdir -p tmp
python code/proof/safe_start.py --limit 128 --output tmp/safe-codes128.json
```

Positive formula recognition certifies derivability in the exact numerical
calculus; negative recognition certifies derivability of an implication to
its designated falsity code. Neither is a theoremhood decision procedure.
The stack recognizer checks the actual repeated Cantor-unpairing encoding.
An accepted formula/stack tuple discharges only the logical Safe premise,
and every startup must still satisfy the entire binary frame invariant.

## Source graph maps and identity collapse

`leaf_cfg.py` accepts a JSON list of `[address, opcode, argument]` leaves.
It validates a full binary tree and compares every guarded successor,
including both decrement guards. Its default map pairs leaves in their
binary-address order; an explicit address map can also be supplied.

```sh
mkdir -p tmp
python code/proof/leaf_cfg.py candidates/layout0/sites.json candidates/layout233/sites.json --output tmp/leaf-map.json
```

`collapse_cfg.py` supports the additional invariant proof needed when the
two certified zero transfer loops are deleted. It defaults to deleting
original leaf indices `6316,6317,6318,6434,6435,6436`, requires every
feasible deleted step to be an identity, rejects deleted cycles, and
compares each surviving edge after finite normalization.

```sh
python code/proof/collapse_cfg.py verification/fusion/zero_specialization/collapseX.sites.json --deleted 6316 6317 6318 --output tmp/collapseX.json
python code/proof/collapse_cfg.py verification/fusion/zero_specialization/collapseT.sites.json --deleted 6434 6435 6436 --output tmp/collapseT.json
python code/proof/collapse_cfg.py verification/fusion/zero_specialization/collapseXT.sites.json --output tmp/collapseXT.json
```

These three supplied source specializations pass the identity-collapse
criterion. X-only and T-only have 6,457 leaves and check 8,384 feasible
retained guarded cases; the combined source has 6,454 leaves and checks
8,383 cases. Each normalization skips at most one identity step. These
are source-language results. Changed binary instruction proofs and a
blank prefix remain separate obligations. For other experiments, the
candidate JSON may contain a `sites` member or be a direct site list.

## File scopes

- `sections/compiler_transfer.tex` proves the finite leaf-map criterion and
  recalls positive-segment halting reflection.
- `sections/safe_start_proof.tex` proves the sufficient formula/stack rules.
- `sections/guard_invariant_transport.tex` states the product invariant,
  the six exclusions, and their transported scope.
- `sections/identity_collapse.tex` proves the finite identity-collapse
  criterion for source specialization.
- `verification/proof/proof_endpoint_audit.md` records the exact inherited
  logical calibration and the distinction between an ordinary ZFC proof
  and a newly compiled proof-assistant endpoint.
- `verification/proof/lowcost/` contains the finite startup search ledgers,
  independent complete bootstrap certificates, pruned runtime row ledgers,
  and exact-bisimulation checks. The ledger `source` paths are relative to
  the archive root; historical scratch prefixes have been removed.

These independent helpers and their mathematical proofs do not supply a
machine with fewer than 246 working states.
