# Initial syntactic-degree replay attempt

Actual session `63492` exited 1 after the author source compiled. The driver
expected a `depends on axioms` report, but Lean correctly reported that the
theorem depends on no axioms. This attempt did not reach an independent replay
and is not passing replay evidence. The original driver and author logs are
preserved; the corrected run uses a separate output directory.
