Runtime-compression checkpoint
=============================

STATUS: No <=217-state Con(ZFC) machine is certified by this checkpoint.
The four217-state tables are rejected prototypes, not research candidates to
be advertised as a solution. They explain why initialized-runtime behavior
and valid blank startup must be checked together.

Reproduce the elementary obstructions with:
    python3 check_runtime_obstructions.py

This script uses only Python3's standard library. It verifies the core's
85-step entry into an infinite rightward blank ray, the exact blank-start
endpoints of the three patched prototypes, and their concrete wrong returns
to the canonical primitive interface after1232 steps. It reconstructs the
expected source CD8 result independently from each initial frame.

runtime_search_report.tex is a LaTeX section fragment for the parent report.
prototype_summary.json duplicates the three individual receipts for indexing.
verification.txt records the last successful checker output.

Recommended supplementary search artifacts, in machine_compression/:
  support_contexts.cpp + support_contexts.log
  ternary_contexts.cpp + ternary_contexts.log
  tworow_loop_synth.cpp + ternary{0,1}.log + ternary{0,1}_verify.log
  helper_repair.cpp + helper_global.log
  global_synth.cpp + global_rank.cpp + global_rank.log
  helper_endpoint.cpp + helper_endpoint.log
  bootstrap_helper_support.cpp + bootstrap_helper_support.log
  joint_marker.cpp + jointall-*.log
  joint_common.cpp + joint_common.log
  joint_prehelper.cpp + joint_prehelper.log
  joint_second.cpp + joint_second_common.log + joint_second_prehelper.log
  screen_compositions.py + compose_screen.cpp
  compositions/screen_results.json + run_compose_global.log + verify_compose.log

The full finite window datasets are reproducible from the scripts, baseline
source snapshot, and independently audited invariant bitmap. They are not
proofs for arbitrary natural register values. Negative search receipts only
exclude the stated bounded template families.

Independent dense-array endpoint audit
--------------------------------------
Run: python3 check_blank_endpoints_dense.py
This compares the entire tape with directly constructed frames for baseline
K218, DMN K218, and the dummy-zero-push omission K218. All three218-state
tables are included alongside. dense_blank_endpoints.json includes hashes
and complete endpoint one-cell locations. It verifies finite startup only.

The first two rejected217-state bootstrap prototypes additionally fail on
the actual first primitive after their own blank startup, after688 further
steps. The third has a separate ternary-invariant-admitted counterexample
in bootstrap-16-ternary-witness.json; no blank-reachability claim is made
for that abstract fixture.
