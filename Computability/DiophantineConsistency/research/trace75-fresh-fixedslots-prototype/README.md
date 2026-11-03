# Fresh-provider trace75 fixed-slots replay

This packet rechecks the already independently reviewed
`Trace75FixedSlots.lean` against the newly rebuilt trace75/BFS union. Its
statement uses symbolic `p0`, `p2`, `p3` equalities and a positive trace75
zero to obtain same-`N` repunit/radix, positive mask, origin digit, and
low/high no-carry slot conditions; `p1` remains arbitrary. This packet does
not establish a carry/halt theorem, iPRA
equivalence, or external file binding.

The runner checks the full 1,977-object union and 80 outside providers,
and compares the additional `CompactMixedIncrement` 9-project-object
subtree against the BFS capture. It checks both exact axiom reports,
no-shadow output root, source pins and serialized direct imports. The
read-only `observations/preflight-attempt01/` passed, and 13 policy controls
passed in `observations/policy-attempt01/`. Historical unrebuilt-source and
package/dynamic ancestry remain inherited limits.

After independent prelaunch review, one fresh-union run passed at
`observations/attempt01/result.json` (SHA-256
`7f1df5657b7a5a82e1136b9d2e19e067c57312c1bbc6ae23dc21e6946ce06873`),
producing `/tmp/trace75-fresh-fixedslots-oyfhiba0/Trace75FixedSlots.olean`
SHA-256 `63c29a06e1efa989917b77548c8362622a038fe0531373a7f86993343f80cda1`.
The object bytes match the earlier build and do not identify unique
provenance. `observations/outer-attempt01/terminal.json` (SHA-256
`4c78ac9fab5a3c8d5da0bbb191932180e0426deef1b9c818c66302990412b2d1`)
records actual child exit 0 and stable inputs/wrapper; the supervising tool
session also exited 0. Independent post-run review passed in
`reviews/trace75-fresh-fixedslots-result-independent/README.md` (SHA-256
`af1caed85f8da4e0462cabacf1cf0eaced427a810f5c2092fa4a16917d28d6f5`).
