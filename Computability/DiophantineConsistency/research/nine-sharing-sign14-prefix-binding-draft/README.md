# Sign14 prefix byte binding: source-only draft

A total fuel-bounded parser proposes to decode five compact prefix files into
the five actual staged Lean residuals, with four ports still symbolic. Each
row theorem would read the bytes using `include_str` at elaboration and prove
parser output equality in the kernel by `rfl`, with no native computation
axiom. The guard must copy and pin the exact files before and after Lean; an
`include_str` theorem concerns the bytes embedded at elaboration, not a live
filesystem. The separately generated prefix packet is independently compared
to the pinned external JSON outside Lean; no theorem about JSON parsing,
fixed-port bytes or the PDF follows. No Lean result is claimed by this draft.
