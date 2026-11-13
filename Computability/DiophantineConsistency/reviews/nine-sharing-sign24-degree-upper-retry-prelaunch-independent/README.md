# Independent sign24 degree-upper local-heartbeat retry prelaunch review

Checker session 15428 exited 0. It verifies the generic source is unchanged
and the only concrete source delta is `set_option maxHeartbeats 4000000 in`
immediately around `expression_syntax_degree`; the option is local to that
theorem. It reconstructs the guard with only fresh-output, manifest and scope
changes and confirms the existing `-M3600`, sampled 4 GiB RSS, 10 GiB host
floor and 120-second limits are unchanged. The previous concrete 200,000
heartbeat failure audit and no-Lean preflight were rerun.

The locally increased heartbeat allowance is explicit and matches the
upstream syntax provider's allowance; it does not prove success. No concrete
Lean degree bound, exact lower bound or external JSON/PDF binding is claimed.
Provider ancestry remains point-observed, and an exclusive Lean slot is needed.
