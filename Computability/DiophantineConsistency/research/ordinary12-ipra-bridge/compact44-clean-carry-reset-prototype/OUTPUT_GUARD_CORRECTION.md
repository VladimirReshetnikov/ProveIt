# Output companion correction

Independent fake-wrapper review of the earlier driver at `8f3167a5f7` found that it accepted unexpected `.olean.private` companions emitted beside both fake output objects. This was an artifact-integrity failure in a no-Lean control, not a demonstrated theorem error.

The corrected driver requires every output companion slot to be absent before compilation and, afterward, requires exactly one regular non-symlink `.olean` with all other companion slots absent. It retains that presence/absence inventory, realpaths and hashes through the final parent audit. `controls.py` exited 0 without Lean: it rejected all ten preexisting output slots, all nine post-output companion additions, all nine corresponding late mutations, and the 12 earlier source/object/report controls. Full independent fake-wrapper review is still required. These are point-in-time checks and cannot rule out a transient change reverted between checks.
