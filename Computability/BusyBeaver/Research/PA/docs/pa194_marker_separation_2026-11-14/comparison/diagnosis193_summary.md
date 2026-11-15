# 193-state audit result

All 54 recognized 193-control spanning action graphs were freshly checked from all 193 possible blank starts: 10,422 cases. Exact outcomes: 110 finite halts, 10,308 outward blank self-loop rays, and four trajectories capped at 100,000 steps. Fifty-two graphs have no capped start. All their intended native-74 starts are rays.

The four unresolved-by-simulation starts lie in two previously rejected designs:

- Coefficient-three calculus: dense starts 0 and 2. Its table has valid physical certificates but its unchanged logic derives contradiction from the numeric collision `E3(1,0)=I3(0,1)=6`. The independent primitive-rule proof verifier was freshly run and accepted 73,393 primitive rows (34,888 restricted-rho instances, 38,503 MP, one Gen, one head5), over 116,171 exact arithmetic terms, ending in 1. Certificate SHA-256 `baf316dce45568036fd803382b30ae2669eb504222a39a6be1f3abcad77dcb83`.
- Rejected loop reassociation: native starts 64 and 74. The stored rejection exposes a changed source graph: a positive constructor branch enters a six-instruction cycle, increments T by four and register 6 by one, and jumps to the cycle start without decrementing its loop test. Its physical startup does not fix the wrong source control flow.

No unexplained 193-state class was uncovered. The dynamic caps are reported as caps; the separate logical/source rejections supply their diagnoses. No global state-count lower bound follows.
