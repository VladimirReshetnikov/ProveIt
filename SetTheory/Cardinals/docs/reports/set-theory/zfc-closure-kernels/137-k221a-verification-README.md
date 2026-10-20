# Verification records

- `clean_replay.json` and `clean_replay_logs/` record the complete initial
  self-contained default replay: PASS in 261.79 seconds. This included fresh
  baseline quick-audit execution, deterministic reconstruction, both positive
  all-tape proofs for each variant, and six exact blank startups.
- `fresh_baseline_quick_replay.json` is that freshly executed baseline driver's
  receipt. It audits stored unbounded-runtime certificates, not a fresh
  derivation of the complete inherited runtime chain.
- `alternate_rows_proof.json` was freshly regenerated after strengthening the
  optimization-mode guard in the macro checker. `macro_posthardening.log`
  records this run and its current checker hash. The proof logic is unchanged.
- `joint_row103.json`, `joint_row157.json`, and `joint_both.json` record the
  independent finite-window proofs, including corrupt-halt negative controls.
- `audit_payload.py` and `payload_audit.json` preserve an additional independent
  structural, positive-diamond, and dense-tape startup audit unchanged. Run it as
  `python3 -B verification/audit_payload.py . /tmp/k221-payload-audit.json`.
- `independent_decoder_*.json` additionally bind the unchanged source to every
  alternative's decoder. The checker is the pinned baseline's
  `portable/verification/check_decoder_binding.py`; the allocation is the one
  reconstructed by the baseline replay, at
  `/tmp/k221-alternatives-replay/baseline_replay/construction/allocation.json`.
  The fresh checker command uses that allocation, `machine/sites221.json`, and
  the relevant `machine/<variant>/k221.native.tm`. These source-decoder receipts
  are supplemental; the all-tape equivalence is the logical transfer proof.
- `supplemental_research_audits.json` records six earlier research audits. It
  does not certify any of the exploratory literal candidates or a 220-state
  construction.

The clean initial run preceded final report/inventory sealing and two
nonmathematical runner hardenings (precise root manifest exclusions and mode
labeling). Release-time extracted-archive auditing is separate. The final
manifest binds every shipped source, table, report, and receipt, and the default
replay checks it before repeating the complete workflow. No stronger claim is
made about fresh runtime derivation than each mode actually performs.
