# Six-edit fixed-snapshot comparison

The guarded comparison returned `MATCHED_PASS` for 107 rows and 11,518 guarded
files. Its receipt matches the independently run peer byte for byte; SHA-256
`95bb022ab43d20dfaed2367d05ce0901da36175293f2da07f469ee9df0f73807`.
The durable marker records the comparator subprocess exit; actual wrapper and
Lean process observations are preserved separately in the terminal packet.

Both Lean runs began with no workspace drift and ended after the later
`ZFCinPA.SeparationKernel` edit. The final comparison also observed that drift.
This is a matched fixed-snapshot result, not a current-source replay. The
848-project ancestor remains author-only; package-transitive and dynamic
ancestry remain inherited.
