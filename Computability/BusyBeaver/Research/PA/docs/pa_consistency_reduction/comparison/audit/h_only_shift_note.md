# Validated h-only Shift intermediate

This is a **196-state intermediate**, not a claimed strict improvement. Full details are in `h_only_shift_note.tex`.

- Table: `h_catalan_node170_3_133_37.tm`.
- Source: `h_catalan_node170_3_133_37_sites.json`, 3811 sites, maximum path length39.
- All4958 all-natural source-site contracts pass with unchanged protected engine rows.
- Independent literal startup:57922 steps, head−2, root75, complete tape equality.
- Complete row patch:37/0=0R11;37/1=1R101;127/0=0R133;127/1=1R20;133/0=0R120.
- Tree: `(A,(B,(T_to_X,D)))` becomes `((A,(B,clear_T)),D)` for A=node36,B=node167,D=node57.
- Command guard changes from `t+h=1` to `h=1`; all normal command effects remain identical.
- Completeness padding: before an old final Shift with t1,h0, substitute AX(0,0,0), then ten Shifts. For h1 append oneShift. Never replay the discarded old finalShift first.
- Soundness uses the syntactic numerical proof invariant and the separate PA proof translation, not a uniform truth predicate.
- All196 states are graph reachable. A subsequent direct-fold search tested33150 candidate deletions and found none.
