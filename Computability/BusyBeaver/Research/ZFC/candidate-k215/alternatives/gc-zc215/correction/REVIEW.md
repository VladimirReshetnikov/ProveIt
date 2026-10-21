# Targeted SB215 / SB215-AB reconciliation

Verdict: both sources retain the known forced-halt return defect. The new fairness argument does not bind to their control-flow graph. No received program was executed.

Package SHA-256: e1ed6e2533508d56051c22f7ffc32cda76af7f6dcc50f0fc119958950554c263.

SB215 native SHA-256 f08bed9e62b9f43237b65c465d2f1bfc17474637b4b02785ca7f1813827bb0ce and source SHA-256 2407f815551b4aba335c9bf041e15e8ce3cfb9ad830d89539f3bcf123462371a match the previously rejected bytes exactly.

AB native SHA-256 2155e318d049ab0c6f578012a0751bc2f445950615a7f035347888e77f7be883; source SHA-256 5369d888be0675221b18fd7bb0df3018213e966265604f9506a6be2c9deff5ba; dense SHA-256 1fff0e90b586ed50dccfcf98f9ff465758ec3cd0357be788049c9d6c8c840ef4. Both native-to-dense state bijections checked exactly against all 430 rows. AB changes precisely native rows 199/1 and 206/0, and source register operands 3 to 5 at ordinals 958, 963, 1136, 1141. Every control edge and the entire post-AX suffix are unchanged.

In both exact sources, ordinal 4697 is CC3 at address 100111. Removing the last three right edges leaves prefix 100, whose first leaf is ordinal 23 (CD3), not scheduler ordinal 0. AX exit ordinal 4589 leads to 4696 (CI6), then 4697, then 23. With the inherited AX exit invariant A=H=X=Y=0, CI6 makes X=1, selector CD3 forces the S block, clear-top consumes arbitrary T, and the restore-X loop writes H=1. The NIP test then halts at 4718. Duration is 15+2T source transitions to CH. This is an arbitrary-natural clear-loop induction with a fixed suffix, not a bounded-simulation inference. Literal probes T=0,1,2,10,100,1000 agree, with a full T=0 trace retained.

The package report's physical.tex asserts AX yields a sound scheduler boundary with X=1. fairness.md section 1 assumes MP/AX then return to residual parsing or fetching. soundness.tex asserts scratch does not change work-tuple equations. All three assumptions fail at this return: X is restored into formula cache before the halt test instead. Good(3) cannot protect against synthetic cache 1. A synchronization theorem for an abstract schedule cannot repair this concrete edge or establish soundness.

Independently replayed both native tables in lockstep for the first 69,744 blank steps: identical, ending (state,head)=(84,-2), with 105 one-cells. Together with the inherited terminating AX contract (unchanged cleanup, and AB's local register-permutation variant) and the supplied all-natural runtime simulation, the same unconditional blank-halting conclusion transports to both tables. This review did not rerun the full symbolic runtime certificates or literally execute the enormous remaining AX arithmetic, nor audit the abstract scanner theorem in isolation. Those are unnecessary to establish the exact source-binding contradiction.

Owned checker: check_exact.py. Machine-readable evidence: EXACT_RECONCILIATION.json.
