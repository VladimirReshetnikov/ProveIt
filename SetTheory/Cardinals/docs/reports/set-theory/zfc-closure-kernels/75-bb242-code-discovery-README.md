# Optional discovery scripts

These Python scripts reproduce the finite local search that suggested the
242-state branch-borrowing construction. They are auxiliary research tools.
The archive's main reproduction path is `code/verify_reduction.py`, which
checks the much shorter ordinary proof certificate and the literal candidate.
The discovery search is not needed to establish the final result.

All dependencies are Python standard-library modules or the adjacent
`audit_tm.py`. In particular, `compensated_search.py` does **not** import
`incoming_routing_search.py`; that script records an earlier, unsuccessful
incoming-only search family. No repository checkout, network access, or
installed package is needed.

When copied to `code/discovery/` inside the archive, both discovery scripts
find `reference/zfc_combined243_old.tm` by searching their parent directories.
An explicit `--input` path works from any directory. JSON results default to
the current working directory; use `--output` to choose their destination.
The original historical evidence files are unchanged. New output records bind
the input table and both executed Python sources by SHA256.

## Reproduce only the selected recipe

Run from the archive root:

```sh
python code/discovery/compensated_search.py \
  --input reference/zfc_combined243_old.tm \
  --expected-sha256 4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300 \
  --dead 15 --keep 27 --bit 1 --radius 5 --bound 64 \
  --output selected-discovery.json
```

This checks exactly one recipe. It reports success, grafting row 15/1 into
27/1, redirecting 11/0 to 27, and retaining the other incoming rows to 27.
`certificate` records each admitted finite window and positive old/new block
lengths. An entry whose source row is unchanged is retained in the result as
an explicitly verified incoming role, not as an additional table edit.

## Optionally reproduce the original full graft family

```sh
python code/discovery/compensated_search.py \
  --input reference/zfc_combined243_old.tm \
  --expected-sha256 4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300 \
  --radius 5 --bound 64 --output complete-discovery.json
```

Omitting `--dead`, `--keep`, and `--bit` enumerates 116,644 oriented recipes.
The historical run found six successes, representing three state-renaming
isomorphism types. A failed recipe is only a failure of this bounded
sufficient-certificate test, and is not a lower bound on Turing-machine size.
The portability preparation did not repeat this broad search.

## Optional earlier incoming-only family

```sh
python code/discovery/incoming_routing_search.py \
  --input reference/zfc_combined243_old.tm \
  --expected-sha256 4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300 \
  --radius 5 --bound 64 --output incoming-only-discovery.json
```

This tries deleting a control by changing only incoming write/move/target
actions. The historical run found no complete deletion. It cannot express
the successful borrowing of a retained state's otherwise unreachable row.

## Scope and provenance

For each proposed graft, the search relates full configurations outside the
two old control roles. Every admitted head-centered window must meet an exact
common configuration after positive numbers of original and candidate moves.
The candidate's internal path uses only explicitly grafted or otherwise
unchanged rows; other patched incoming rows are allowed only as subsequent
checkpoints. All reads and writes remain inside the known window, so its
unknown exterior remains arbitrary and unchanged. The admitted windows
overapproximate all windows reachable from the blank input.

The final ordinary proof strengthens this finite-window discovery argument
to arbitrary function tapes at initial state 95 using a small explicit
inductive invariant. It is that direct argument which supports the relative
machine theorem in the report.

`audit_tm.py` is copied byte-for-byte from ProveIt commit
`e58338db7545909907e07a7603e8eb88625c527a`, path
`Computability/BusyBeaver/Research/ZFC/audit_tm.py`. Its inherited license is
included as `LICENSE.ProveIt.txt`. The two discovery scripts were created in
this research session; their portable copies preserve the search algorithms
and add archive-relative input resolution, explicit output paths, provenance
hashes, argument validation, and the optional `--bit` restriction.
