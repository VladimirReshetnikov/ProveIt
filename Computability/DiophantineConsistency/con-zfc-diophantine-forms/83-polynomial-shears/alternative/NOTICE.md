# Attribution and scope

The included `selector/horn_shared_source.json` is an unchanged source-data
copy from `ConZFC_Structural_Reductions_Round11_2026-10-24.zip`,
`con-zfc-structural-reductions-round11/commutative/horn_shared_source.json`.
Its SHA-256 is
`bef85fcf1fbd70fc109162b5b518fe7c4803a54864c867c64f3e6ea7e3be71cf`.
That file inherits the branch-shared C222 Horn source from ProveIt package68,
`68-joint-positivity/direct/horn_shared_source.json`. Its mathematical
calibration belongs to the cited upstream work.

The pairing polynomial used in `gadgets` is the two-witness max-square
pairing from incoming `ZFC_Diophantine_Joint_Guards_2026-10-24.zip`,
`certificates/LOCAL_GADGET_PROOFS.md`. This contribution does not claim that
pairing identity as new. New pieces are the natural nonnegative masks,
joint quadratic zero/predecessor graph, their composed graph improvements,
and the natural-selector/stutter-deletion refinement.

The local generators and mathematical notes in this folder were authored
for the current research iteration with AI assistance. They are research
artifacts, not independently peer-reviewed results. Universal mathematical
proofs and exact arithmetic checks are included; no new Lean/Rocq kernel
certificate is claimed.
