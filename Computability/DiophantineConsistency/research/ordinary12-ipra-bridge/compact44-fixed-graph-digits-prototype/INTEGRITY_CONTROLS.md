# Direct-object and frozen-source controls

Independent fake testing of the earlier driver at commit `f39bdad65f` reported two accepted mutations: symlink compiler outputs and a frozen-source mutation during the peer side after that source's per-step check. Those were failed negative controls, not Lean builds.

The hardened driver requires every output object to be a regular non-symlink file. Before each dependency scan and compiler step, it records all direct object and companion slots (including absent slots), their realpaths and hashes, checks them after the scan and compiler, and retains guards through the end. It checks every frozen source after both sides and again after the final parent audit. `integrity_controls.py` exited 0 without Lean, accepting regular unchanged files and rejecting eight cases covering changed/removed direct objects, a late companion, changed realpath, missing/symlink/directory outputs and a late frozen-source mutation. The exact-axiom and Init-object focused controls also exited 0. Full independent fake-wrapper testing is still required.

These are point-in-time observations: they cannot guarantee detection of a transient mutation that occurs and is reverted between checks. The sampled resource and package/dynamic-ancestry limitations in the replay plan also remain.
