# Reviewer note: what is new in AX11GH

**AX11GH fills a specific gap in the current command-interface matrix.** It combines the explicit AX generalization binder `U(c,h)`, the eleven-entry/four-operand AX protocol, and the cache-only Shift guard `h=1`. Its closest predecessors each lack one of these combined choices. AX11G has the explicit binder and AX11 but retains the sum guard; QAX11H has AX11 and the cache guard but retains the offset binder `U(d,h)`; GH/GHS has the explicit binder and cache guard but retains the ten-entry/three-operand AX protocol.

This is operational materiality beyond control-graph novelty. AX11G and AX11GH disagree on the single Shift command from `(t,w,d,h)=(1,0,0,0)` and also disagree in the reverse direction from `(1,0,0,1)`. Against QAX11H, choosing first operand `c=1` with incoming `d=h=0` changes the saved universal formula from code 2 to code 10. The two source instructions implementing that difference are the decrement at address 95 and restoration increment at 100: they select register A instead of D. These are the source bindings checked in the new report and verification artifacts.

Against GH/GHS, the new AX pushes the guarded gate and falls through the full MP parameter reader. The fourth operand `z` is consumed and survives as the output offset; old GH's AX clears its offset. The extra generated stack entry changes all selector distances and the compiler's Push/Pop/generalization words. In the cache-only interface, the final refutation detector must be Pop; a plain Shift does not detect visible top 1 with cache 0. The new Pop has twelve Shifts after a zero-operand AX, compared with eleven for GH.

AX11QH4L/R does not already implement this source change. Those two designs preserve the entire QAX11H source and its offset-binder command semantics while changing four-increment decoder association. They are therefore adjacent physical decoder alternatives, not the missing combined command protocol.

**AX11GHS shares AX11GH's abstract semantics.** Its distinct implementation prepares comparison operands `(1,h)` instead of `(h,1)`, with the same live and halted files. It is appropriately presented as a second implementation of the new interface, not another new numerical calculus.

The novelty claim should be narrow and explicit: a new jointly checked composition of attributed mechanisms, with two concrete binary blank-start graphs and adjusted command compilation. It is not a claim to invent the G binder, AX11, Q exchange, or cached guard, nor a claim to introduce a fundamentally new proof-search architecture. The current census and exact full-tuple comparison separately establish that neither new graph is a renamed/reflected/complemented/alternate-root form of any of the 110 spanning historical representatives. The sole disconnected diagnostic is excluded by the spanning invariant.

## Exact references

All historical paths are pinned to `VladimirReshetnikov/ProveIt@1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`.

| Interface | Archive and precise member |
|---|---|
| AX11G | `docs/incoming/pa194_ax11g_research_2026-11-14.zip!pa194_ax11g_research_2026-11-14/proof/ax11g.tex` |
| AX11H/QAX11H | `docs/incoming/pa194_ax11h_research_2026-11-14.zip!pa194_ax11h_research_2026-11-14/proof/ax11h_preservation.tex` and the archive root README |
| GH/GHS | `docs/incoming/pa194gh_research_2026-11-14.zip!pa194gh_research_2026-11-14/machines/PA194GH/proof.tex` and the archive root README |
| AX11QH4L/R | `docs/incoming/pa194_ax11qh4_research_2026-11-14.zip!pa194_ax11qh4_research_2026-11-14/README.txt` |
| New AX11GH/GHS | This release's `proof/relative_ipra.tex`, `verification/check_commands.py`, and `verification/check_source_commands.py` |

The small report-ready table is `new_design_position.tex`.
