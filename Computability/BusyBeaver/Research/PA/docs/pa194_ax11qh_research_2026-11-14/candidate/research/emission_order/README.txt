Emission-order grammar search

The seven separately emitted theorem heads can be reordered without changing the generated numerical calculus; selector indices must be adjusted. This run searches reassociations and all pairwise exchanges of those seven blocks, retaining the initial U/rho prefix and the guarded gate suffix. It starts from the two supplied AX11 grammar seeds. It uses exact compatibility of simultaneously applied two-cell history folds whenever the reader frontier is near the target, rather than trusting bipartite matching alone.

Run with C++17:
  c++ -O3 -std=c++17 search.cpp -o search
  ./search seeds.txt leaf_attrs.txt output 240 14112026

The time stopping rule makes exact proposal count machine-dependent. The recorded run tried 3,631,115 proposals and found no count below 194. It does not establish a state lower bound, nor was an unverified numerical score promoted to a construction. The source is adapted from the supplied PA194AX11 grammar search with a new emitted-head permutation operation.

The companion run uses hseeds.txt, replacing six fixed transitions by the new H controller rows. Reproduce it with ./search hseeds.txt leaf_attrs.txt h_output 90 14112027. It considered 1283873 proposals, accepted 221857 moves, and again found no score below60 (194total). Its exact log and parameters are retained.
