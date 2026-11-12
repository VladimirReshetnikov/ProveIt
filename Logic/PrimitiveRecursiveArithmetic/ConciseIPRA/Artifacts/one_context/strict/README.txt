SCOPE FACTORIZATION FOR COMPLETE iPRA CHECKERS

This supplement factors a strict public-goal validator into a shape check
and the unchanged proof kernel's initial no-image scope opening. It preserves
the exact accepted finite JSON certificate language of each paired module.
It changes no axioms, rules, proof instructions, internal raw aliases, or
fresh-name operations. The universal proof is in proof.tex.

Recommended small pair (ordinary elimination, Eq/D public goals):
  reference/control_shared_strict_eqd.py: 824 normalized bytes.
  code/checker_eqd.py:                  803 normalized bytes.
  Tokens: 373 -> 359. AST nodes: 426 -> 414.
  Gzip level 9: 460 -> 463 bytes (informational, not minimized).

Additional ordinary pairs:
  Eq/Q/D goal validation: 873 -> 863 bytes.
  Full exact integer/list certificate typing plus Eq/Q/D: 1049 -> 1039 bytes.
Crossed-elimination versions are also supplied and measured separately.
Do not compare 803 bytes with the distinct permissive compact 522-byte
public-input-contract frontier; those modules charge different interfaces.

All reference modules are unmodified extracted files from the authenticated
incoming archive ipra_reversal_core_2026-11-11.zip in ProveIt commit
a4e5e96c456303cf231eab2aeeb3291d8889833f, path
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/incoming.
The archive's exact Git blob SHA1 is:
14280baf9ddbe82201b5bc23ebd93100ec973915.
Their source SHA256 values are recorded in metrics.json.
The incoming package itself records comparison commit
1517d9d79ce33f631e0f82960c849427cbba23bf.

Run with Python 3.12:
  python3 reproduce.py

The reproduction script uses only Python's standard library. It remeasures
all complete files; creates reproducible normalized-source .py.gz files;
checks that every candidate is identical to its paired comparator outside
the goal-validator definition; runs normal and optimized-mode process
comparisons; and checks the scope-factorization identity on finite examples.
Proof producers and these regression checks are not imported by any checker.

Recorded result: 984 processes, 492 paired comparisons, no mismatch.
Old outcomes: 198 acceptances and 294 rejections. Two sets of 15,781 parser
comparisons also have no mismatch. These finite checks support the code;
the proof in proof.tex supplies the universal exact-language theorem.

The implementation theorem is relative to the inherited comparator's
soundness and completeness contract. No new full Lean/Rocq verification
of the Python checkers or arithmetic/native bridge is asserted. This is
a small implementation simplification, not a new arithmetic basis or a
proof of absolute minimum.
