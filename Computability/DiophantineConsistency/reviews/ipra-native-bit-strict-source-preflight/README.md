# Native-bit strict historical source preflight

The historical-basis planner actually exited 0 at workspace HEAD
`1925463aa0fb2bfab0253ab51acdc611fcefbca9`. It checked frozen parent source
bytes and workspace drift for 1,096 used parent modules, selected all eleven
additional modules, reported 15 drifts, and found no untracked or modified
additions. The complete plan and its hash are retained here.

This is a point-in-time source plan; it does not authenticate parent objects,
run Lean, or establish dynamic/package ancestry. A real replay must generate
a fresh strict plan at its own stable HEAD and retain all 1,210 parent rows.
