# Prepared AQ16 historical pair retry

Run 01 terminated with actual outer exit 143 for an unknown reason; its
[interruption evidence](../ipra-aq16-historical-interrupted-run-01/README.md)
does not establish a successful pair. This script is byte-for-byte the pinned
run-01 launcher except for a fresh `/tmp/ipra-aq16-historical-paired-run-02`
output path. Its SHA-256 is
`239d46d7460c2127b2fa74feeea463a3793374f2871f3facfc10d228f772e161`;
it passed `bash -n`. No partial run-01 peer artifact is reused: the existing
preparer makes new sibling seeds from the authenticated original parent.

The termination cause was not observed, so this is a controlled retry rather
than a diagnosis. To reduce overlapping workload, start only after the live
direct14 paired run has finished, verify available disk and memory immediately
before launch, and use low CPU and idle I/O priority. At preparation time,
`df -h /tmp` reported 11 GiB available and `free -h` reported 17 GiB available
memory; these point-in-time readings do not identify the earlier cause or
guarantee a later run. The existing per-stage disk-reserve checks still apply.

Coordinate stable HEAD through preparation, capture the actual full outer
terminal result, preserve any failed run without overwriting it, and require
independent complete artifact validation after a successful coordinator result.
This retry has not been launched.
