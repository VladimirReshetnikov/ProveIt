# First Pell ordinate square bound

`DirectMainPellGrowth.square_bound` proves in every IΣ₁ model that `Q>0`, `n≥3`, and `k=2*ycoord n (2*(Q-1)+1)` imply `Q²≤k`. It uses monotonicity and two elementary Pell recurrence growth steps. This is an abstract conditional result; the graph-specific join is separate.

`run-pellgrowth.py` produced `observations/pellgrowth-attempt01/` with exit 0 and no reported warnings. Source SHA-256 is `b784c30c5fd69efe9e0837c6d2d7bb3bc2f05ce219be5dc2ab040c5a7231ca03`, output object is `50eda5030c35ee0dc81c5d9bfc7544c5983958a028686ee405b16ae58cacff8c`, and the axiom report lists `propext`, `Classical.choice`, and `Quot.sound`. The projection object and selected 1,291-object union were pinned and rechecked. Package, dynamic, and source-to-object ancestry remain inherited rather than freshly rebuilt; resource samples and exact pins are in the receipt, and temporary paths may disappear.
