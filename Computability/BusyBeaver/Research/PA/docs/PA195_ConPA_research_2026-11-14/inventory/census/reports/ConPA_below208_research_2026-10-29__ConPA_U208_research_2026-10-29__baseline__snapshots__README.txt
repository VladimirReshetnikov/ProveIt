PORTABLE COMPARISON SNAPSHOTS

Five U209 and nine U208 native/dense table presentations are retained with
their exact source address tables. There are two rooted labeled transition
graph isomorphism classes at each state count. The nine U208 presentations
come from five supplied packets; all use the same 172/211 history fold.

Run from the delivery root:
  python3 -B code/compare_snapshots.py --output /tmp/snapshot_comparison.json
  python3 -B -O code/compare_snapshots.py --output /tmp/snapshot_comparison_opt.json

manifest.json records original workspace-relative source paths, source ZIP
SHA-256 identities, archive member paths, retrieved commit, expected class,
and exact SHA-256 for every retained file. A source_path is provenance only;
verification opens only the portable local path. Original notices are kept
under notices/ with their source-relative directory structure.
