# Source148 selected fresh reproduction

Work on a fresh recovered copy with Python3 assertions enabled; unset `PYTHONOPTIMIZE`, and do not pass `-O`. The package's top-level verification wrapper and checksum-manifest command are outside this replay. No proof-assistant or broad search is needed.

Our exact actual commands, interpreter, working directory, 60/300-second process bounds, elapsed times, executable hashes, stdout/stderr and required JSON statuses are preserved in `replay1/result.json` and `replay1/logs/`. The original submission remains unchanged. The own harness is `replay_selected.py`; it copies the received tree, deletes each targeted old receipt before its leaf runs, and stops on failure. Its original-archive path is explicit. To reproduce after archive recovery elsewhere, substitute that one path in a separate adapter and preserve the diff.

Run in this order inside the working copy:

```
python3 -B research217_encoding/crossover30_table.py
python3 -B research217_native_basis_review/replay_h_pw.py
python3 -B research217_native_basis_review/replay_hkp_s.py
python3 -B research217_mixed_tag_basis/check_fixed_code4.py
python3 -B research217_pairing_macros/prove_zero_flow.py
python3 -B research217_bootstrap/bind_crossover30.py
python3 -B research217_bootstrap/prove_crossover_blank_ray.py
python3 -B research217_bootstrap/prove_crossover30_tags.py
```

The additional `bind_crossover30.py` invocation regenerates the complete raw218 blank startup and its five exceptional tags before the distinct crossover217 runtime, avoiding reliance on the old delivered context record. It must report the accepted root seed `[3,0,0,0,3,0,0,0,0]` at step312909. This startup belongs to raw218; the next check proves the folded217 blank ray at step85.

The last receipt must say `ALL_INITIALIZED217_CASES_AND_CONSERVATIVE_TAGS_PASS`, with 6167 cases, 1515251 symbolic rules, 434 covered rows, minimum positive clock12 and zero unknown windows. The exact ordered case file must have SHA-256 `24cb25432fd8389c24e293cbe4ef4001f1ad3f50238d6859763509aaeca5809f`. These are initialized primitive contracts, not a successful blank217 initialization. The first leaf must say `PREFIX_PASS` and zero novel primitive entries; its internal two-second helper cap can produce `NOT_PROVED` even with process exit0. Preserve any such outcome before considering a separate successor attempt.

The short certificate leaves verify ten explicit H/PW MPs, the 97-row H/K/Peirce-to-S certificate, seven-node mixed-system code4 certificate and codec-independent scratch invariant. They do not themselves prove the complete uniform logical/calibration or codec theorem; the ordinary appendices supply those arguments. The run deliberately skips the unchanged primary delete301 runtime, historical runtime wrappers, manifests, allocator searches and report build.
