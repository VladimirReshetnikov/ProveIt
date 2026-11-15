# Verification evidence and scope

The current release result and dependency boundary are stated in the root
README and `report/report.pdf`.

- `final_replay/` and `final_replay.log`: completed final default replay of
  all five new constructions, both parent contract bindings, affine clocks,
  and novelty against 110 prior graphs. Default mode does not regenerate
  universal symbolic contracts or check the imported arithmetic derivation.
- `final_physical_replay/`: final integration evidence for all seven full
  physical component replays: 33,456 outcomes and 7,607,530 symbolic events.
  The first root-wrapper invocation completed the five original-primary
  checks, then exposed a receipt-family label mismatch (`baseline` versus
  temporary directory `primary`). The wrapper now preserves `baseline`.
  The remaining two AX11H replays and construction/clock checks completed
  separately, with byte-identical contracts, lemmas and receipts. The
  original log and exact correction are retained; a complete seven-table
  wrapper rerun after that metadata correction is not claimed.
- The machine directories contain completed full independent literal-row
  contracts and their receipts. The root `--physical` option regenerates
  all seven sets (five new machines and two parents) in isolated copies.
- `ax11h_absolute_audit.*`: focused manual review of the revised AX11H
  written absolute calibration, including exact upstream file hashes and
  explicit review limits. This is an attributed mathematical dependency,
  not a new proof-assistant kernel endpoint.
- `ax11h_upstream_quick_replay.json`: successful upstream finite checks;
  physical contracts were separately regenerated for AX11H and LC_AX11H.
- `RELATIVE_IPRA_REVIEW.txt`: ordinary mathematical review of the original
  primary and four source-preserving loop variants, preceding LC_AX11H.
- `GAX11_REVIEW.txt`: historical review of the independently reconstructed
  GAX11 command argument. The final census identifies that graph as a
  duplicate of newly delivered AX11G; it is not one of the five new graphs.
- `initial_replay/`, `reproduction_log.txt`, and
  `all_five_novelty_log.txt`: preserved initial-snapshot evidence. Their
  five-candidate novelty set was four LC variants plus GAX11, against 94
  references. Final novelty is in `../late_snapshot/novelty.json` and
  `final_replay/novelty.json`: five LC variants including LC_AX11H, against 110.

The release-wide `SHA256SUMS` binds every preserved receipt and contract.
The finite verification scripts do not assert that they check a complete
arithmetic derivation. The report supplies the relative iPRA proofs and
the LC_AX11H absolute corollary importing the archived AX11H theorem.
