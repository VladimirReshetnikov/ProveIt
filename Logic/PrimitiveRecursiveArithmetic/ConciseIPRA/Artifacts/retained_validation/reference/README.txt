These files document the inherited basis and the measured comparisons.

control_intrinsic.py is the exact actual-binding checker from the incoming
ipra_intrinsic_validation_2026-11-13.zip package at the pinned repository.
It is 316 tokens / 360 AST nodes / 591 normalized bytes.

control_nodes.py and control_tokens.py are actual-binding whole-document
controls from ipra_names_and_scopes_2026-11-13.zip. The node control supplies
the incumbent exact-binding AST coordinate of 358. Its packet schedule is
not interchangeable with all of the other controls.

NativeBiInterpretation.lean is an unchanged identification module from
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA at commit
e0d702b905c74b74a23d045f8289b151bb8ebcff. It imports NativeRoundTrip and
BiInterpretation; those full dependencies are in the repository. This copy
is NOT represented as a self-contained Lean project or as verification of
the new Python code.

upstream_base.tex and upstream_certificates.tex are unchanged source
chapters from the unified article at the same commit. They are supplied
for offline inspection of the imported theory and checker arguments, not
as required inputs to compiling the new standalone report. Their own
labels/macros require the upstream article preamble.

The inherited source license is preserved in LICENSE-ProveIt.txt.
