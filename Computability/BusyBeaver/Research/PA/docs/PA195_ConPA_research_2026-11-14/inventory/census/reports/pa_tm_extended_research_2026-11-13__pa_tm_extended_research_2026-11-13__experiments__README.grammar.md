# New bounded experiments

Place this directory as `experiments/` beside the parent report package's `verification/` directory. The shared verification directory supplies `core.py`, `grammar.py`, `layout.py`, and `flexible_core.py`, bound to the published PA196 input and the frozen reduced-product invariant certificates. No network or Git access is used.

Run commands from this directory:

- `python3 flex_mutants_reduced.py`: replay the final 232,848 one-row fold candidates with the reduced-product and numerical-interval physical checker. It preserves the protected engine rows. The expected result is no survivor. This takes approximately two minutes after invariant preparation on the original machine.
- `g++ -O3 -std=c++17 search.cpp -o search` followed by `./search 300000`: stochastic grammar search over role/order variants, with four randomized RePair parses per proposal. The expected best raw grammar size in the recorded run is 70.
- `python3 dictionary_search.py`: dictionary-assisted reparse of 50 local logical variants.
- `python3 assemble.py dictionary_candidates.json 20000`: sample associations of those dictionary parses and score compatible context folds.
- `python3 noop_family.py`: score 1,518 insertions of existing scratch-zero loops around safe AX macro subtrees. The minimum recorded state estimate is 197.
- `python3 joint_anneal.py`: extended joint grammar/role search. The preserved run was interrupted after 560 completed cycles of 3,000 iteration slots; its best effective AX-reader cost remained 62. The script's configured limit is longer than the frozen run.

Generated scripts overwrite their local experiment receipts and logs; use a copy if preserving the supplied evidence. The files ending in `_result.json` and the supplied logs record the actual completed runs. None is a proof of minimality. The three fold receipts cover the same 232,848 tables under successively refined conditions, not three disjoint candidate families.

`words.py`, `noops.py`, and the grammar scripts descend from the prior incoming research packet and add the new joint role/reassociation and no-op searches. Their ordinary mathematical scope and the four accepted same-size tables are explained in the main report. The C++ program is discovery code, not trusted proof code. No engine-invalid candidate is included here.
