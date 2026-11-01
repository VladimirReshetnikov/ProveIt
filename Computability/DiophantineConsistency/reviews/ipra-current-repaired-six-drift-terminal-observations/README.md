# Six-edit replay terminal observations

The builder agent reported that author tool session 31511 exited 0 with
`PASS /tmp/ipra-six-drift-replay-729okjpa`; the root agent observed peer
session 46919 exit 0 with `PASS /tmp/ipra-six-drift-replay-42b7hj5k`. Both
states contain 107 successful rows, no initial workspace drift, and one final
drift: the later `ZFCinPA.SeparationKernel` edit.

The builder agent observed author comparison-wrapper session 3334 exit 0;
the root agent observed peer wrapper session 45144 exit 0. Both printed
`PASS_COMPARATOR_EXIT_0`. Their separately recorded child comparator markers
and byte-identical comparison receipts report 107 matched rows and 11,518
guarded files. The JSON files here pin the actual tool-session observations;
they are not themselves in-process exit recorders.

These are fixed-snapshot results. The inherited 848-project ancestor remains
author-only, and package-transitive/dynamic ancestry remains as recorded in
the input packet. The later SeparationKernel edit requires another rebase for
a current-source claim.
