# Exact symbolic kernel split

`CompactKernelSplit.kernel_split_generic` proves, without hypotheses and
without expanding the kernel, that for every natural radix `r`,

```
paramKernel r = r^8849 + lowerKernelAt r
```

where `lowerKernelAt r` is the weighted sum of all terms below the isolated
top digit. For the actual `rho = 2^67`, `lower_lt` proves
`lowerKernelAt rho < rho^5496`: the sparse coefficient bounds apply to the
lower terms, all of whose positions are below 5496.

The checked `CompactKernelLowProduct` client transfers the split and bound
to every model of IΣ₁. If `x < 2^(67*3297+1)`, it proves that the exact
symbolic product's low half modulo `2^590069` equals
`lowerKernelAt rho * x`, and that this value is below `2^(67*8793+1)`.
The separate compact cell product client proves the input bound for the
actual base and pulsed cells. This result does not yet prove the whole
cell-plus-block bound or a complete packing condition.

Attempts 01–03 exited 1: initially two missing explicit radix reductions,
then kernel memory exhaustion in a specialized split. Attempt 04 checked the
generic split and the lower bound but failed on an unnecessary specialized
wrapper at the configured recursion limit. No object from these failed
attempts is accepted. Attempt 05 (session `64652`) removed that wrapper and
exited 0 without warnings or `sorryAx`; the three named axiom reports contain
only `propext`, `Classical.choice` and `Quot.sound`. The run uses the same
recorded mixed project-provider construction as the compact cell product
bound, checking overlap bytes and before/after hashes. Its direct-import
guards and provider overlay were unchanged. Logs, failed source snapshots,
commands and hash inventories are retained. It is a single-author
incremental check with inherited source/object, transitive, package,
dynamic-loading and between-observation ancestry, not an independent paired
replay or authenticated full closure; `/tmp` paths may be ephemeral.

The first model low-product attempt failed on a recursive congruence tactic;
the corrected attempt `low-product-attempt02`, session `62122`, exited 0
without warnings or `sorryAx`. Its five named axiom reports contain only
`propext`, `Classical.choice` and `Quot.sound`. Direct-import guards and the
same 517-name, 338-overlap mixed project overlay were unchanged across the
run; this author-side incremental client inherits the ancestry limitations
above.
