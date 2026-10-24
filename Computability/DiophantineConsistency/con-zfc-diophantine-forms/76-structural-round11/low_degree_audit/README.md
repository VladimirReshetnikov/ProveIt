# Independent low-degree audit

For the distributed release, run from any directory:

    python3 path/to/low_degree_audit/audit_literals.py --release
    python3 -O path/to/low_degree_audit/audit_literals.py --release

This reruns all exact polynomial, graph, degree, coefficient-reconstruction, payload and inherited-file-hash checks. It additionally matches the retained proof/source files to the hashes in the prior full archive audit. RESULTS_RELEASE.json explicitly records that the original archive ZIP hashes are not recomputed in release mode. The original full-mode RESULTS.json, ARCHIVE_MATCHES.json and SOURCE_ARCHIVE_PINS.json preserve the completed archive verification evidence, including SHA256 and Git blob pins. A stored provenance receipt is not a substitute for rerunning archive authentication when independent archive bytes are available.

If all eight incoming ZIPs and review/ARCHIVE_PINS.json are present in review/archives/, omit --release to authenticate every archive SHA256 and Git blob hash again and compare each inherited file with the exact archive member. NORMAL.log and OPTIMIZED.log record those successful full runs. RELEASE.log and RELEASE_OPTIMIZED.log record successful release-mode runs.

The checker uses only Python's standard library and never imports producer code. It needs the sibling positivity/ and positive/ directories, and these review/packages inputs:

* 69-cones-pell/positive/PROOF.md and equation.json.
* 70-residue-orientation/eleven/PROOF.md and p11_positive_degree325.json.
* 70-residue-orientation/positive/section.tex.
* 73-guard-reanchoring/positive/PROOF.md and p13_degree30.json.

AUDIT.md gives the mathematical review. The inherited_interfaces/ copies are unchanged extracts of the incoming source archives, retained for the precise normalized-rank, signed auxiliary-index, and positive auxiliary-reconstruction interfaces used in the audit. Their exact archive origins and hashes are in ARCHIVE_MATCHES.json. They retain their original upstream attribution and licensing; see the corresponding original sources and positivity/inherited/source71_LICENSE plus positive/native/licenses/.
