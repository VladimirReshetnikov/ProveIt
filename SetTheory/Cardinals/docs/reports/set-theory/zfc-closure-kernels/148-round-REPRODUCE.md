# Verified targeted replay

Use Python 3 with assertions enabled: do not use -O or PYTHONOPTIMIZE. Only Python standard-library dependencies are required by the seven verified commands. The received tables, source lists and certificate data are read as inert files. No received repository code is imported or run.

First check the original archive:

    python3 -B verify_manifest.py

Make a separate working copy before rerunning anything: the drivers overwrite their own result JSON. The following named commands were run in a clean copy with the archive's directory layout and selected dependencies:

    python3 -B research217_encoding/crossover30_table.py
    python3 -B research217_native_basis_review/replay_h_pw.py
    python3 -B research217_native_basis_review/replay_hkp_s.py
    python3 -B research217_mixed_tag_basis/check_fixed_code4.py
    python3 -B research217_pairing_macros/prove_zero_flow.py
    python3 -B research217_bootstrap/prove_crossover_blank_ray.py
    python3 -B research217_bootstrap/prove_crossover30_tags.py

The last command is the full unbounded symbolic runtime/tag proof and took roughly two minutes in this environment. It must report ALL_INITIALIZED217_CASES_AND_CONSERVATIVE_TAGS_PASS, 6,167 cases, 1,515,251 symbolic rules, 434 covered rows, minimum duration constant 12, and no unknown windows. Its regenerated INITIALIZED217_TAG_CASES.json must have SHA-256 24cb25432fd8389c24e293cbe4ef4001f1ad3f50238d6859763509aaeca5809f. Wall-clock fields in summary receipts naturally differ between runs.

The short commands establish exact crossover source/prefix binding, the ten fixed H/PW MP steps, the 97-row H/K/Peirce-to-S proof, the fixed seven-node native code4 proof, the codec-independent scratch invariant and the exact 85-step blank-ray prefix. Ordinary mathematical obstruction and codec proofs also require reading their arguments; a fixed numeric certificate alone does not verify a uniform consistency theorem.

replay_results/REPLAY_RESULT.json records tested script hashes and outcomes; its logs preserve output. This profile validates its own dependency closure. Broad source/machine searches were not repeated. Do not execute all Python files indiscriminately: some are historical exploratory searches, run on import, or need omitted regenerated source expansions. The bounded 60-second source census can naturally stop at different points on another computer; the recorded tested receipts, not a new timing run, specify the original stopping scope.

## Report rebuild

With a normal complete LaTeX installation containing article, geometry, fontenc, lmodern, microtype, amsmath/amssymb, booktabs, longtable/array, xcolor, enumitem, fancyhdr, hyperref, needspace and xurl:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

PDF_QA.json identifies the distributed PDF/TeX and the final rendered-page review. Rebuilding need not reproduce identical PDF bytes because creation metadata can differ.
