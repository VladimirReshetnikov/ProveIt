# Formalism-emitter experiments

These scripts are unchanged snapshots of the source-emitter experiments described in the report. `manifest.json` gives their hashes and the hashes of the selected measurement receipts. They generate source programs and exploratory incremental compilations. Their provisional compiler outputs are **not validated machines**; the final report and the main `machines/` directory identify the only two fully replayed new tables.

The scripts locate pinned predecessor directories relative to their own file location. To rerun them, extract the three bundled archives alongside these scripts, preserving the original top-level names. From this directory:

```sh
unzip ../../vendor/K219_Construction_2026-10-20.zip
unzip K219_Construction_2026-10-20/portable/vendor/K220_Construction_2026-10-20.zip
unzip K220_Construction_2026-10-20/portable/vendor/K221_Construction_2026-10-20.zip
```

Then use Python 3.10 or newer with assertions enabled, for example:

```sh
python3 -B row_permutations.py
python3 -B compose_membership219.py
```

The scripts write new result directories next to themselves. Some searches are substantial; no timing guarantee is implied. The inherited `orientation_postfix`, `h_fusion`, and source/compiler modules are supplied by those exact archives. The scripts set `K220_BASE` and `K221_BASE` themselves to these local paths.

`fixed_k.py`, `one_fixed_k.py`, and `predecessor_private.py` measure the positive fixed-binder specializations. `fixed_k_repair.py` explores alternate closed-atom parses. `row_permutations.py`, `row_permutation_pairs.py`, and `rho6_row_orders.py` measure exact axiom-range reparameterizations and row orders. `rho8_membership.py` and `compose_membership219.py` produce the conditional membership-U sources. `fused_t_explosion.py` measures the still-uncalibrated fused T-plus-ex-falso row. `nested_codec.py` records a separate exploratory encoding route.

The three retained 205-node sources are in `../conditional_membership/`. Their lower consistency implication remains open. The validated exact rho6 source is in `../../machines/rho6_219/`; its compilation and runtime are checked by the main portable replay rather than by these discovery scripts.
