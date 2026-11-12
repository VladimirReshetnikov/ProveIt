# Proposed compact symbolic-port 78↔85 model comparison

This unelaborated source wrapper composes the separately proposed positive
84↔78 model comparison with the symbolic compact-port 84↔85 wrapper. The
port tuple is `[beta,K,low,beta+high]` with arbitrary natural K, and beta
positivity is obtained from the existing symbolic port-bounds interface. Each
existence assertion quantifies an all-positive 14-slot model valuation.

This is not an elaborated model equivalence, iPRA theorem or external-file/PDF
binding. Both imported source chains and their transitive providers still need
guarded Lean verification and coherent ancestry. The checker inventories the
composition and replays both source receipts; it does not invoke Lean.

Independent source review is recorded in
`../../reviews/ordinary14-78-85-compact-model-composition-draft-independent/`.
