# Independent review: same-source rational-66 pair replay

The read-only `check.py` exited 0. It rechecked the replay's 676 recorded direct and producer guard entries, separate observed outer session 32461 exit 0 and child exit 0, and prior-run receipt pins. The recorded command uses the identical Lean source and the recorded search path is the same historical provider path. The complete compiler/axiom log and actual output object match the original byte for byte; the output path is separate.

This is a same-source, same-provider replay. It is not a fresh source-closure rebuild or independent reconstruction of historical transitive, dynamic or package ancestry. Resource monitoring is sampled. The replay repeats the two-conjunct theorem described in the [original independent review](../normalized106-rational66-pair-independent/README.md): an external rational-evaluator zero iff and a separate iPRA derivation for the integer syntax, with the same fixed port tuple. No Lean replay was run during this audit.

SHA-256: `check.py` `361cf1701432303d25438270eb95227e61dd9b1cfa1b95f26c087238171aae7f`; `result.json` `9a95bf44eae3fcf7769a4a5456347716719c7430f8a87f33450d45dc8b14975e`.
