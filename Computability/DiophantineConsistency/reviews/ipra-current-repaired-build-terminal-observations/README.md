# Fixed-snapshot replay terminal observations

The author tool session 54236 returned exit code 0 and
`PASS /tmp/ipra-current-repaired-build-rlsymfuh`. The root agent reported that
peer tool session 72004 returned exit code 0 and
`PASS /tmp/ipra-current-repaired-build-y6kamkla`. The JSON files record these
tool-session observations and the corresponding final state hashes; they are
not in-process exit recorders or independent comparison receipts.

Both states report 258 successful rows and no source drift at the initial
workspace observation. Each final observation reports the same six changed
workspace sources. Thus these are fixed-snapshot results, not a current-source
proof. Guarded comparisons and inherited ancestry qualifications remain
separate.

The author comparator wrapper session 40047 and the root agent's peer comparator
wrapper session 14303 each returned exit code 0 and
`PASS_COMPARATOR_EXIT_0`. Their JSON observations pin the respective durable
child-exit markers. Both independent comparison receipts match byte for byte;
each reports 258 matching rows and 10,148 guarded files. The final workspace
match flag is false because of the six post-snapshot edits.
