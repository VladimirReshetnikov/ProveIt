# Temporary replay retention, 30 October 2026

The shared filesystem became full while the isolated HA dependency build and
other checks were active. To recover space, the following terminal, interrupted
temporary overlays were removed after verifying that they were not active
providers or planned replay parents:

- `/tmp/adaptive86-machine-compat-rebase-v11-7zdhtdd8`;
- `/tmp/ha87-focused-validator-rebase-f7u7wyte`, `v4nzh026`, `9sdv9uuy`,
  `6qpfw2_p`, `qhd75h_b`, and `a88xpkx7` (each suffix has the same prefix);
- `/tmp/ha87-focused-validator-rebase-5zvm8dzr`, `85slsco9`, `qzmw9m5q`,
  and `mjkn7d92` (same prefix).

The v11 failed-state evidence, and the HA runs' terminal states, source
deltas and verified-row logs, were frozen in their existing review packets.
The four nonempty interrupted HA overlays' raw temporary objects were removed,
so those objects cannot now be rehashed in place; the recorded hashes remain
historical evidence, not an independent replay. The six zero-record attempts
had no verified objects. Live builds and accepted provider parents were not
removed.
