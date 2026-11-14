B8 PARITY SOURCE AND LITERAL RUNTIME INTEGRATION

This experiment has 202 working states. It does not meet the requested <196
bound and is not a completed blank-tape PA-consistency construction.

Run python3 build_b8.py (Python standard library only) to regenerate the
raw207-state and folded202-state sparse-labeled tables, source tree and
5205 uniform source-instruction checks. Working controls are the labels
appearing in the first column; start is0 and terminal label is196. Some
working labels are numerically greater than196, so do not infer the state
count from the largest label. Direction symbols are L/R. The default
physical tape alphabet is{0,1}, blank0.

The change integrates all of: multiplier8 in every cons occurrence (including
MP and compound AX macros), equality tag4 instead of3 at five emitted sites,
the previously proposed sum-parity acceptance routine, and the longer return
scanner. Implication/membership/universal tags are0/1/2. The AX macro word has
206 tokens rather than201. The whole source has4062 primitive sites.

The symbolic executor checks unbounded unary runs and uses the unchanged
register-engine contracts from the upstream paper. This is executable
mathematical evidence, not a new Lean/Rocq kernel certificate. Arithmetic
semantics of the altered source macros and a correct blank-start boundary
are separate proof obligations. In particular, a ten-million-step startup
inspection finds clean frames with gap40 and nontrivial registers; it does
not establish an admissible initialized proof-search store. No nonhalting
inference is drawn from that bounded inspection.

Inputs Program.lean,Conjugacy.lean,pa196.tm are byte copies from ProveIt
1fe9b29810bfe3d0e507146d65f6b97692e7444a, jamesyc-upstream/pa196.
The AX grammar was the existing parity_encoding_best.json in the prior
research workspace (search receipt: conpa_tm_study/research/search_receipts/
parity_encoding_result.json in docs/incoming/conpa_tm_study_2026-11-13.zip).
The grammar is included completely here. Its old heuristic score200 was
not an integrated table count; the integrated validated runtime count is202.
