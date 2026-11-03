# Incomplete second halt attempt

The runner exited 1 after launching Lean because its `ps` resource parser
raised `ValueError: invalid literal for int() with base 10: '<defunct>'`.
The runner did not catch that exception or record the child exit. Its exact
source and runner are retained here. The fresh temporary output root was
`/tmp/xq91-halt-l_3l4dhm`; at later inspection it had no compiled object and
empty stdout/stderr. A subsequent process-list check showed no command for
that temporary root. The Lean PID and exit status were not captured, so
neither the child's result nor a resource-monitor pass is asserted.
