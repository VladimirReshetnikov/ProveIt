# Independent review: arbitrary-port R=31 partial seed

PASS for the finite partial seed, not a checked graph zero. No Lean run was performed in this review.

Using a separately implemented second-order Pell ordinate recurrence `y₀=0`, `y₁=1`, `yₙ₊₂=2a yₙ₊₁−yₙ`, the independent checker recomputed the two exact positive intervals, first Pell square, phase/size inequalities, `XY | k−R−1`, `H | X(3c−2X)+2` with positive quotient, and `X<c`. The pinned Lean recurrence advances at ordinary Pell base `b+2`; therefore the seed's first base `2P+1` matches parameter `2(P−1)+1`, the source ordinate uses base `Y(X+1)+2`, and the actual ordinate uses base `Y(X+1)+1`.

The checker independently evaluated every one of the 74 candidate rows with the finite trial `i=T=n=1`, confirmed `q=2`, `R=31`, `F+C=q` and the exact signed-binary output digest. That trial output is **nonzero**. The ports are `(beta,K0,MC,MF)=(1,1,28,0)`, which violate the fixed symbolic-port bound `0<MC<beta`; no fixed-BFS claim follows.

The numerical inputs match the displayed scalar premises proposed for `Trace75UnscaledReverseData.reverse_data` under the ordinary-to-shifted Pell base correspondence, including the source interval witnesses. The purported existential transfer of the resulting same tuple to a positive 74 zero remains a mathematical proposal: neither that concrete specialization nor the boundary-specific graph binding has been Lean checked. In particular this finite nonzero trial is not a counterexample to an existential graph equivalence, an iPRA result, or evidence of a full 74 zero.

The seed script SHA-256 is `d46fcda0011422f6bd534bb45260f8d461f537a231ce9dcc8d1052107bbf21f1`; its observation SHA-256 is `bcaf04a0f6651682c5e016748a90dbcdcd3b15bf5b9a14dea62530155238dd93`. Exact independent computations are in `check.py` and `result.txt`.
