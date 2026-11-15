# PA194LC_AX11H

A new 194-state composition of the loop-continuation reassociation with the latest PA194AX11H machine. It preserves all 3,671 resolved source instructions and changes three native transition rows. Dense table SHA-256: `5f10f071e7118ff33aba822e05bae0331b4c78508656c3e945c31b0c6788f9c5`.

## Reproduce

Use Python 3.10+ with assertions enabled and no third-party packages:

```sh
python verify_all.py --output /tmp/lc-ax11h-evidence
```

This rebuilds all tables and source artifacts, checks exact byte equality, independently replays all 4,778 source outcomes for each of the parent and new literal tables, checks each complete blank startup, and verifies the exact affine-clock bound and six-transition loop cost difference. `--quick` omits both physical replays and duration checks and records these omissions. Frozen outputs are never overwritten by the wrapper.

The complete precomputed evidence is under `independent/results/`, `receipt.json`, `duration_receipt.json`, and the replay logs. The parent table and source are frozen under `parent/`; `parent_integrity.json` binds their hashes. `integrity.json` binds the verification inputs and outputs. `proof.tex`/`proof.pdf` contain the relative iPRA proof; `proof_fragment.tex` supports inclusion in the main report.

## Mathematical scope

This supplies an ordinary computer-assisted proof of relative halting and nonhalting equivalence in iPRA, with cross-machine witness bound `57922 + 13*(t+1)^2 + 681*(t+1)`. It does not supply a compiled Lean endpoint. The parent packet at latest commit `603c58ca3bd6bf3222fcfc4e308e6b079f65d573` supplies a separate written absolute PA calibration; that theorem remains a separate premise for transferring the desired equivalence with Con(PA). The construction makes no sub-194 claim.

See `PROVENANCE.json`, `UPSTREAM_NOTICE.md`, and `licenses/` for upstream attribution. Novelty evidence is supplied by the main report census, including the latest incoming archives.
