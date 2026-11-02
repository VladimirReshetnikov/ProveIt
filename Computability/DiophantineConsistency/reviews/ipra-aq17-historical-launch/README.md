# Prepared AQ17 paired launcher

`launch-historical-pair.sh` is the independently reviewed runbook's shell
block with the original parent observation and matched pair-state hashes
filled from the separately observed and audited AQ29 parent. Its SHA-256 is
`76e3244b7de9930d7c193bac8f1e68819efc651a7811562d4c97229dbf87541f`.
It passed `bash -n`. At preparation time, the three parent evidence pins
matched, the run-01 output path did not exist, and all 76 inputs pinned by
the [independent AQ17 workflow review](../ipra-standard-aq17-independent-workflow-audit/README.md)
still matched. That review's actual process exit was 0 and its receipt has
SHA-256 `dda81452d71ad96ad06c8a20cbaedbe25ae8f0ba4daba825aadb0d8f0d549323`.

Run this script from the repository root only after coordinating a stable HEAD
through planning, freezing, and preparation. Its parent authentication gate
must still pass; the checks reported here are not a substitute for it. Capture
the actual outer exit and full output, and preserve any failed attempt without
overwriting it. After a successful coordinator result, a separate independent
complete artifact audit is required. This preparation is not an AQ17 paired
run and makes no current-source or inherited external-ancestry claim.
