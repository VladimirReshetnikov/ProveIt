# Private split Wang-table replacement: author build

The generated private replacement compiles the original `ArithmeticWangTable` tail with the full chunked finite-predicate facts imported from the independently replayed provider. This is a private build only; it does not replace the repository source, the canonical provider, or the still-running original worker. Complete exported-interface comparison remains a separate gate.

- Build: `/tmp/adaptive-wang-table-split-b9zuak6s`, **PASS**, Lean exit 0, 16.7 seconds, empty full log.
- Exact draft source SHA-256 `6066b1d0ffbece89bc007d0888a7622c121220083979405fc03c58502a3eec93`; original source SHA-256 `8bf620443a3ed74892efba1aeaa6f8c14add5feaff4954dda001a6acf5e36ff2`.
- Result object SHA-256 `6006dc15ea57fb14fd9cab2e7d3388eed879fe55524487e45cc8dfff77352dee`; full log SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- The driver authenticated before and after all 26 source/object/log records of peer provider `/tmp/adaptive-wang-chunk-full-042v1clo`, plus 356 inherited source guards and 1,717 canonical selected objects. The private overlay is a symlink copy with the old WangTable output excluded.
- Reproduce the pinned source using `python3 Computability/DiophantineConsistency/research/wang-chunk-full/generate_table_draft.py`; build with `python3 Computability/DiophantineConsistency/research/wang-chunk-full/build_table_draft.py` from the repository root. These private providers under `/tmp` are required.

Evidence is in `adaptive-wang-table-split-author-evidence/`; its 8-file `FILES.json` SHA-256 is `e8b1a637a439c648b8a7b07aba1f8c0296cc109493ce73cca05f086b68c9e9de`. An independent replay passed and matched the source, object and full log; see the independent receipt. The generator records that the replacement tail is copied byte-for-byte, but compiling it does not by itself establish the full public interface or validate the historical object's source provenance.
