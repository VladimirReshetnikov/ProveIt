# Independent prelaunch findings for the original coefficient driver

The exact driver at commit `735a95d668`, SHA-256
`5c332bba21db5e236f8a254916c8e62fd721b6179484ad3beb6e3d57b10e515a`,
was **not cleared** for a real paired replay. The independently exercised
full-loop controls found two guard issues. These are driver-isolation
findings, not evidence of a false arithmetic theorem.

1. The driver verifies empty seed target slots before copying, but after the
   copy it records the current target companion state without requiring every
   non-`.olean` companion to remain absent. A fake copy injects
   `.olean.private` immediately after each seed copy; the unmodified driver
   accepts both fake compiler children and emits a receipt.
2. The driver checks the client output directory only after copying the two
   seed objects. A fake overlay provides a symlinked module directory pointing
   to a separate controlled temporary directory. The driver rejects before a
   fake compiler starts, but only after both seed files have already been
   copied through that symlink outside the intended overlay.

The exact original driver and both self-contained fake reproducers are
retained under `observations`. Each command below actually exited 0; `PASS`
in this packet means that the **undesired behavior was reproduced**, not that
the driver passed review. Both tests use only fake parent, dependency and
compiler operations and controlled temporary directories, and launch no Lean.

```
python3 -I -S -B Computability/DiophantineConsistency/reviews/compact44-coefficient-decomposition-prelaunch-defects/observations/seed-copy-companion.py
python3 -I -S -B Computability/DiophantineConsistency/reviews/compact44-coefficient-decomposition-prelaunch-defects/observations/seed-parent-symlink.py
```

The author has been asked to require every post-copy non-object companion to
be absent and the copied `.olean` to be an ordinary non-symlink file, guard
the full snapshot through final checks, and verify the output directory
before and after each copy. A corrected driver requires new full-loop controls
and independent exact-byte re-review before any real pair. Existing initial
loader, point-in-time, package/transitive/dynamic and sampled-resource
boundaries remain.
