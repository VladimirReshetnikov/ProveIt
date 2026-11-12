# 84 own-zero scalar rank window — source draft

This unelaborated source proposal applies the existing internal
`scalar_rank_window` to the natural rank from the positive 84 graph's own
zero. It keeps beta positivity, all-positive valuation, four explicit port
casts, and mask bounds `MC<beta`, `MF<2*beta` as hypotheses; actual compact
port instantiation is separate. It proposes `24≤R`,
`R+q³+q+1≤q⁴`, and in particular `R+1<q⁴`. The guard gap supplies the
required scalar restriction and the rank formula is compared algebraically.

This is not a proof of the stronger `26≤R` required by P72Exact, and does not
establish the auxiliary norm, the exact Pell index, a compiled theorem, provider
ancestry or an iPRA endpoint. Physical-file/PDF semantics remain separate.
The checker tests 500 finite scalar-window instances and replays the natural
rank source receipt. It does not run Lean.

Independent source review is recorded in
`../../reviews/ordinary14-84-rank-window-draft-independent/`.
