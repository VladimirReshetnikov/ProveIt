# Direct-BFS finite conjugacy: first attempt

The pinned-input generator builds a concrete candidate for the horizontal/vertical color and row-index maps between the original and direct-BFS tables. The original monolithic Lean check `observations/directbfsconjugacy-attempt01/` did **not** pass: `mergeSort` did not reduce under `decide`, and the 943-row check hit the 3-GiB kernel memory limit. No conjugacy theorem is claimed from this file. The exact failed source, runner, diagnostics and receipt are retained.

A separate array-backed base, bounded proof chunks, size/distinguished facts and coverage runner are in the adjacent `direct-bfs-lean-conjugacy-{base,chunk,shape,coverage}-prototype` packets. Their checked samples and any completed sweep are the only Lean evidence; the candidate's externally generated maps alone are not a formal bijection or tiling/machine interpretation theorem.
