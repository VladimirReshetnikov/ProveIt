# Existing-dispatcher and packet-transport checks

The native audit separately replayed all 76 archived group packets through
`verify_normal_cut_group_handlebodies`; see `saved_group_packet_replay.json`.
The packaged `tools/verify_packets.py` uses the existing public dispatcher
`verify_normal_cut_handlebodies`, whose new schema branch calls that checker.
Two additional checks exercise this adapter and both actual packet layouts:

| Report | Packet | Result |
| --- | --- | --- |
| `dispatcher_replay_figure_eight.json` | `certificates/figure_eight.json` | Verified |
| `dispatcher_replay_binary_16384.json` | `certificates/group/binary__1__16384.json` | Verified |

The second packet has a 16,385-bit coordinate. It is read with the established
hexadecimal integer transport and is never expanded into its sheets. Each
report binds its packet bytes and all loaded native source modules by SHA-256.
These are replay checks, not additional producer outputs or timing samples.

`dispatcher_transport_checks.json` records sixteen focused adapter checks.
Twelve reject malformed packet representations: duplicate keys, floating
coordinates, boolean coordinates, decimal-string coordinates, `NaN`, positive
and negative infinity, ambiguous layouts, a non-object packet, a wrong row
length, a boolean source identifier and a missing certificate. The remaining
four check an equivalent hexadecimal source, rejection under a zero recorded
operation cap, rejection of a boolean certificate rank, and a malformed CLI
invocation that exits with code 1 and writes a failed report.

Reproduce these checks from the unpacked delivery directory:

```sh
python tools/verify_packets.py --fast-root /path/to/integrated/fast --packets certificates/figure_eight.json --output results/dispatcher_replay_figure_eight.json
python tools/verify_packets.py --fast-root /path/to/integrated/fast --packets certificates/group/binary__1__16384.json --output results/dispatcher_replay_binary_16384.json
python tools/audit_packet_transport.py --fast-root /path/to/integrated/fast --output results/dispatcher_transport_checks.json
```

To replay all 76 through the dispatcher, omit `--packets` from
`verify_packets.py`. The saved adapter check intentionally avoids repeating
the full native replay already completed in the same run. Neither tool invokes
an elimination producer or relies on Regina. These checks exercise integration
and exact transport; the source topology and algebraic certificates remain
the responsibility of the documented independent verifiers and mathematical
proofs.
