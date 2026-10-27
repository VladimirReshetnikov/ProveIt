# Reference implementation provenance

`code/reference_balanced_packing.py` is copied byte-for-byte from:

* Repository: https://github.com/VladimirReshetnikov/ProveIt
* Commit: `ab2fbc9e03d5c3d0ad6dec8686960bfe498b0b06`
* Archive: `docs/incoming/eth_asymmetric_packet_balancing_2026-10-26.zip`
* Member: `eth_asymmetric_packet_balancing_2026-10-26/code/balanced_packing.py`
* SHA-256: `5e899df4fd25b1371fe6f42c13f87caba49637fb92da0f12b12dd01a831bb6d2`

The repository license is reproduced unchanged in `LICENSE-ProveIt.txt`.
The reference is executed only by the explicit comparison and benchmark
programs. Its original input validation, greedy row assignment, score
formula, tie breaking, and checks remain unmodified. The replacement uses
the same contract and caches row sums/cell powers as proved in the report.

The main preprint and other reports are identified in the source manifest
and bibliography, not redistributed wholesale in this package. The report
credits the imported mathematical ingredients separately from new schedule
choices and implementation changes.

Closing check: the same file is present byte-for-byte at commit `474ddba696a5d385c091c23fb2995f69edd13e00`,
under `Computability/SubexponentialSAT/Research/eth_asymmetric_packet_balancing/code/balanced_packing.py`.
