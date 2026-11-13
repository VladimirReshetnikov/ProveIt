# Simple 80-graph size bound

`Direct80Size.x_lower` proves `X≥16` from the explicit model inequality `beta≥15` and the positivity of the graph valuation. It uses only `q=beta*J+1` and `X=w*q`; it does not require a graph zero or expand the large fixed numeral. The actual fixed-port calibration `beta≥15` is separate.

The selected-provider author run `run-size.py`, `observations/size-attempt02/`, passed in session 24840 with exit 0. Attempt01 failed on an additive-order rewrite and is retained. Exact source, commands, selected prototype pins, output and resource samples are in the two observation directories. Provider, package-transitive, dynamic and historical source/object limitations are inherited, and no independent Lean replay is claimed.

Receipt review found the original runner hashed sibling `run.py`, not itself. The unchanged source was rerun with self-pinning `run-size-v2.py`: `observations/size-attempt03/` passed in session 16676 and produced the bit-identical object at `/tmp/tenpositive-80size-wu3437c5/Direct80Size.olean`. The original receipt does not establish its own runner's stability.
