# Terminal failure

Author-observed outer session 87971 exited 1 with `FAILED RuntimeError('compile failed Sign32DirectExpression')`. The first stage dependency check exited 0, but its Lean compile exited -6; its complete compile log reports a Lean `memory_exception` at `interpreter` under the existing `-M2800` limit. The monitor reported no external stop reason and sampled peak session RSS 2,939,711,488 bytes. No first-stage object exists, and the second endpoint stage did not run. No declaration in this client is counted as proved. The exact elaboration or evaluation operation that triggered the memory exception is not established by this log.

State, logs and author-recorded outer outcome are retained here. Limits were unchanged. A fresh bounded split may localize the failure; no endpoint is claimed.
