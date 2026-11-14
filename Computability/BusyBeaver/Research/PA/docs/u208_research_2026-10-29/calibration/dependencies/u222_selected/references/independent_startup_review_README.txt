INDEPENDENT LITERAL STARTUP REVIEW
================================

Usage (Python 3.10+, standard library):

  python3 review_native_bootstrap.py --table TABLE --sites SITES \
      --startup STARTUP_RECEIPT --out NEW_REVIEW_RECEIPT

All four paths are command-line inputs. TABLE is the native-label transition
table, SITES its complete source-leaf list, and STARTUP_RECEIPT the literal
startup trace produced by validate_native.py. The script imports no project
runtime module and does not execute the primary arbitrary-register checker.
It uses explicit exception guards, which remain active with Python -O.

This reviewer is specific to the inherited native state convention:
start0, dispatcher84, external halt254, and physical register permutation
(6,2,0,4,3,7,8,5,1). Use the native presentation, not a densely relabelled
table. The native-to-dense bijection is a separate check.

OUTPUT FIELD SCOPE
------------------
status=INDEPENDENT_LITERAL_STARTUP_PASS:
  All checks below succeeded. This status alone does not assert universal
  primitive simulation or logical consistency calibration.

table_sha256 / sites_sha256 / startup_receipt_sha256 / reviewer_sha256:
  Bind the exact input bytes and the reviewer source. They establish identity,
  not mathematical correctness on their own.

working_states / transition_rows / graph_reachable_working_states:
  Direct syntax census, totality on two read symbols per working state, and
  directed-graph reachability from start. Graph reachability is not a claim
  that every state is visited in the actual blank run.

halt_label / start_label:
  The exact native convention; all transitions to an undeclared state go
  to this one halt label.

site_count / full_binary_prefix_tree / maximum_depth / operation_counts:
  Source-leaf syntax, uniqueness, complete binary-prefix coverage, depth<=64,
  and valid register/loop arguments. This does not check that those sites
  came from the intended proof-search source; use the separate source audit.

expected_symbolic_cases:
  One case per non-decrement site and two per decrement. This is a required
  case count, not a claim that those symbolic cases passed.

startup_steps / first_calibrated_root / startup_state / startup_head:
  Exact blank execution, with every supplied trace transition independently
  checked against the table. No earlier suitable root frame occurred.

startup_gap / startup_registers / spare_count / spare_values:
  The independently decoded complete final root frame. Current/stack/cache
  registers must be zero. Calibration of the other register values is a
  separate source-enumerator theorem.

every_startup_trace_row_replayed / complete_finite_support_compared:
  Every transition of this finite prefix and its complete final set of
  nonblank cells were checked. The rest of the two-sided tape is zero.

four_induction_block_schema_rows_match:
  The twelve literal rows supporting the four arbitrary-v block scans agree
  with the direct mathematical derivations in the runtime review. Universal
  validity follows from those unary inductions, not from sampled block sizes.

For the main machine theorem, additionally require the complete arbitrary-
register runtime report, the exact source audit, the proof-enumerator
calibration, the theory interpretation, and the state-renaming check.
No proof-assistant kernel certification is asserted by this script.
