# Boundary binding drafts: bounded heartbeat increase

These remain conditional source drafts. They copy `../trace74-boundary-parent-binding-v2/` byte for byte except for one added `set_option maxHeartbeats 8000000` in `Trace74BoundaryGraph.lean`. The prior guarded author attempt recorded its first four stages PASS, but the Graph stage hit Lean's default 200,000 heartbeat limit; that complete failed attempt is retained. This option changes the elaboration budget, not the theorem statement. The retry retains the 3 GiB Lean cap, runtime guard and 600-second per-stage timeout.

No Graph theorem is accepted until the separate guarded retry and audit pass. Even a successful conditional binding would not certify the R=31 finite instance or a fixed-port zero.
