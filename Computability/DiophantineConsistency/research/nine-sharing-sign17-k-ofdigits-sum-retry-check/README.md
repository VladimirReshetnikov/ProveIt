# Generic radix-digit sum retry

This fresh, single-stage guard proposes the arbitrary-base natural-number identity relating `Nat.ofDigits` on a finite vector to its little-endian weighted sum. It does not assert a concrete K, byte, JSON, gzip, file, or PDF binding.

The sole Lean source change from the independently audited failed attempt is removing `generalizing v` from induction on `n`; Lean had reported that `v` was automatically generalized. The earlier failure is preserved in `research/nine-sharing-sign17-k-ofdigits-sum-check/attempt01/` and independently reviewed at `reviews/nine-sharing-sign17-k-ofdigits-sum-failure-independent/`. A clean printed axiom report in that failed module is not a compiled theorem.

The guarded runner retains the audited Fin942 provider, direct import and Init provenance checks, one Lean thread, per-stage time and memory caps, and host-availability checks. The no-Lean preflight exited 0 and reported `PASS_NO_LEAN_PREFLIGHT`; no Lean result is claimed yet. The source SHA-256 is `93c7205049b6d110e45f67bf2aa3f6e3521d3738946b8892e742aa02d76b6b5f`; runner SHA-256 is `f5ff7127b21e028cfc591d3286bdc2624b2dff5164d68e8310b5e7d5bd19fc02`; manifest SHA-256 is `097a646e95d90f8c0cdcdc07541dc9894b30d4f525ad4221cba23926816ef395`.

Independent prelaunch passed: `reviews/nine-sharing-sign17-k-ofdigits-sum-retry-prelaunch-independent/`. It checks the source delta, failed receipt, provider routes and bounded no-Lean preflight. Lean execution remains pending exclusive allocation.

Attempt 01 completed with observed outer session 76603 and exit 0; the generic sum and postflight passed. See `attempt01/`. Independent terminal audit is pending.

The [independent terminal audit](../../reviews/nine-sharing-sign17-k-ofdigits-sum-retry-terminal-independent/README.md) passed; the attempt packet is frozen.
