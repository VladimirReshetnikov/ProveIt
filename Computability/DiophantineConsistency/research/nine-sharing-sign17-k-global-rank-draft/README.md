# Global candidate-rank transport: source-only draft

`Sign17KGlobalRankConditional.lean` proposes two separate theorems: transport
adjacent numeric comparisons through the checked Fin942 weight equality, and
apply the checked actual-map criterion to the Fin942 candidate vector under
explicit Start, nonzero and global adjacency hypotheses. This source is not
yet guarded, reviewed or compiled; no global candidate-rank theorem is
claimed. Source SHA-256:
`4c7f932d5ac882d9e60312dd46f9b56bd3e2d1f9a0436f61449e7c142256fb69`.

One possible assembly route is to prove Start separately, divide the 941
nonzero positions and 940 adjacent pairs into bounded contiguous finite
chunks, and combine each family using a generic `Fin.addCases` theorem. This
would include cross-block pairs explicitly and avoid a quadratic global
comparison. Whether direct kernel evaluation of the nested `Fin.append`
candidate vectors fits the existing limits at scale is untested; the
[first 16-case offset probe](../nine-sharing-sign17-k-global-rank-probe-check/README.md)
passed Lean and independent audit. Alternatively, an assembly
can use the independently checked local block and boundary theorems, but it
must establish their exact relation to the single Fin942 vector. Neither
route has been checked. Full K coefficient aggregation and external
file/gzip binding remain further obligations.
