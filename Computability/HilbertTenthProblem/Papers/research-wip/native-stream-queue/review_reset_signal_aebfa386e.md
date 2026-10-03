# Signal/reset intake review: portable replay index

The full mathematical and source reviews are in [the corrected signal note](review_conservative_signal_corrected_aebfa386e.md) and [the reset-net note](review_reset_petri_net_aebfa386e.md). Both original author suites pass with all 129 archived members unchanged. The reset note identifies two malformed-input defects and supplies the narrow [guard repair](reset_net_exact_domains.patch); all fourteen author commands also pass on the repaired private copy.

[The independent checker](review_reset_signal_aebfa386e.py) and its [saved receipt](review_reset_signal_aebfa386e.json) accept explicit extracted package roots. It embeds all 45 signal and 84 reset member hashes, executes imported sources from authenticated bytes rather than cached bytecode, restores the temporarily replaced module names, and keeps author writes in temporary copies. Neither ZIP is modified. Source hashing is performed before imports or subprocess runs. Extraction is deliberately outside this helper: use the intake wrapper's safe, hash-checked extraction, or independently reject traversal, absolute paths and symlinks before supplying roots.

```sh
python3 review_reset_signal_aebfa386e.py \
  --signal /absolute/path/to/conservative-signal-release \
  --reset /absolute/path/to/reset-net-release
```

The default performs the independent complete closure/branch checks, literal net identities, paid schedule accounting and boundary regressions, and compares them with the saved receipt. It does not repeat the saved author command ledger. Add `--author` to rerun the twelve corrected-signal commands (ten original plus the normal and `-O` correction checker), fourteen original reset commands and fourteen repaired reset commands. Every original member is then compared against its pin. In the patched run only the two repaired source files and their two exact digest values in `checks/PADDING_AND_GENERIC_PEAK_RESULTS.json` may change. No whole metadata fields are ignored. `--write` explicitly regenerates the receipt; omit it for read-only receipt verification.

The repair regression can also be repeated with assertions disabled:

```sh
python3 -O review_reset_signal_aebfa386e.py \
  --signal /absolute/path/to/conservative-signal-release \
  --reset /absolute/path/to/reset-net-release --repair-only
```

It rejects 32 malformed inputs and verifies nine complete unchanged valid schemas. This is a boundary regression, not an assertion-disabled replay of the author's assertion-based proof audits.

The separately completed old-versus-corrected signal comparison uses the preserved old evaluator from archive `Conservative_Signal_Diophantine_Frontend.zip` and the new bundled `correction/verify_packet_correction.py --original`. The original evaluator is not executed implicitly by this helper. That comparison passed 1,200 full formula checks, 72 sections and 66 malformed-call cases, and confirmed that the corrected code is byte-identical to the prior reviewed repair.

Two bounded arithmetic opportunities are checked in the notes: a natural-only signal slack projection saving 1,449,018 coordinates and 7,489,424 paid operations in the specified complete sparse-affine schedule; and a natural-only reset gate simplification saving 761 additions per externally selected source step. Both retain explicit external horizons and do not constitute a fixed-arity universal-equation record.
