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
actual base and pulsed cells. The bound leaves 13 completely unused radix
digits and 66 further unused bits below the `2^590069` boundary.

`CompactKernelBlockSize` adds the complementary exact high-half identity:
for the same size-bound hypothesis, `K*x / 2^590069 = 2^(67*42)*x`.
Consequently, for **any** model cell function whose values at every index
below positive `N` satisfy that size bound, Lean proves the complete
`cell_sum` field `X j + blk j < 2^590069` for each `j<N`. The cyclic
predecessor and stride indices are below `N` because `N>0`. The earlier
compact-cell and pulse-size results can supply the pointwise size premise;
this generic client does not itself construct a row word, a full packing,
high-mask facts, graph zero, or an iPRA theorem.

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

An independent source inspection caught an explanatory comment in the
successful attempt 02 that overstated the slack as fourteen whole radix
digits; the theorem's explicit exponent was already correct. The prior exact
source is preserved with its observation. The comment was corrected, and the
guarded sole-Lean rerun `low-product-attempt03`, session `43180`, exited 0
with no warnings or `sorryAx` and unchanged direct and overlay guards. Its
five axiom reports have the same three metatheoretic axioms as attempt 02.

The first `CompactKernelBlockSize` attempt proved the high-half lemmas but
failed at the last four-term exponent rewrite; its source and log are
retained. Corrected attempt `block-size-attempt02`, session `38121`, exited 0
without warnings or `sorryAx`, with the same three metatheoretic axioms in
all three named reports. Its guarded mixed overlay covered 524 distinct
project-file names, 339 names present in multiple providers and 338 present
in all three; all overlapping hashes matched, and the overlay and sampled
direct guards were unchanged. It has the same single-author and inherited
ancestry limitations as the other clients.
