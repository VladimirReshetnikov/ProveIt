#!/usr/bin/env python3
"""Recover the two complete batch-162 packages and verify their placed bytes.

Read-only Git access; new external output only. No proof/compiler/test run,
network access, checksum-manifest interpretation, or line-ending conversion.
Source 62 audits the exact 247 table; source 63 gives its 246-state successor.
Python 3.10+ and Git are sufficient; invoke without -O.
"""
from __future__ import annotations
import argparse
import io
import json
from pathlib import Path, PurePosixPath
import stat
import subprocess
import sys
import zipfile

HOST = "SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels"
# Explicit original-member -> placed-file map generated from the placement map.
# File inventories include archive-only articles/PDFs so original layouts return.
PACKAGES = {62: {'slug': 'audit247',
      'archive': 'docs/incoming/zfc-prefix247.zip',
      'arrival': 'f94653113962b4c7d446c7d0cbd3b03a69d534da',
      'root': 'zfc-prefix247',
      'files': ['Makefile',
                'NOTICE.md',
                'PROVENANCE.json',
                'README.md',
                'code/affine_engine.py',
                'code/build_machine.py',
                'code/check_boot_canonical.py',
                'code/check_boot_independent.py',
                'code/check_instructions.py',
                'code/check_literal_instructions.py',
                'code/check_macro_inductions.py',
                'code/check_marking_independent.py',
                'code/verify.py',
                'exploration/README.md',
                'exploration/boot_search.cpp',
                'licenses/LICENSE.ProveIt',
                'licenses/LICENSE.Wade',
                'machine/canonical_table.tex',
                'machine/renumbering.json',
                'machine/zfc_prefix247.tm',
                'machine/zfc_prefix247_old.tm',
                'reference/Prog254.v',
                'reference/baseline252_old.tm',
                'reference/lean/Bisim254.lean',
                'reference/lean/ChoiceCalibration254.lean',
                'reference/lean/DirtyProgram254.lean',
                'reference/lean/L2Lib254.lean',
                'reference/lean/NativeTheory254.lean',
                'reference/lean/Prog254.lean',
                'reference/lean/RegisterPath.lean',
                'reference/lean/RegisterPathClean.lean',
                'reference/lean/SiteCoverage.lean',
                'reference/lean/WFTheory.lean',
                'reference/prefix250_old.tm',
                'reference/prior/affine_engine250.py',
                'reference/prior/check_macro_inductions250.py',
                'reference/prior/prefix250-audit-README.md',
                'reference/prior/prefix250-audit-provenance.json',
                'reference/upstream-attribution.md',
                'report.pdf',
                'report.tex',
                'results/all_symbolic_instructions.log',
                'results/bootstrap-canonical.json',
                'results/bootstrap-independent.json',
                'results/bootstrap-search.json',
                'results/canonical_sparse_bootstrap.log',
                'results/independent-proof-review.md',
                'results/independent_dense_bootstrap.log',
                'results/independent_literal_instructions.log',
                'results/independent_marking.log',
                'results/instructions.json',
                'results/literal-instructions.json',
                'results/logical-review.json',
                'results/macro-inductions.json',
                'results/marking-independent.json',
                'results/pdf-review.json',
                'results/rebuild.json',
                'results/reconstruction.log',
                'results/regeneration-and-portability.json',
                'results/universal_macro_inductions.log',
                'results/verification.json',
                'sections/macro_proofs.tex',
                'sections/reduction_and_calibration.tex'],
      'placed': {'Makefile': 'code/62-audit247-Makefile',
                 'NOTICE.md': '62-audit247-NOTICE.md',
                 'PROVENANCE.json': 'data/62-audit247-PROVENANCE.json',
                 'code/affine_engine.py': 'code/62-audit247-code-affine_engine.py',
                 'code/build_machine.py': 'code/62-audit247-code-build_machine.py',
                 'code/check_boot_canonical.py': 'code/62-audit247-code-check_boot_canonical.py',
                 'code/check_boot_independent.py': 'code/62-audit247-code-check_boot_independent.py',
                 'code/check_instructions.py': 'code/62-audit247-code-check_instructions.py',
                 'code/check_literal_instructions.py': 'code/62-audit247-code-check_literal_instructions.py',
                 'code/check_macro_inductions.py': 'code/62-audit247-code-check_macro_inductions.py',
                 'code/check_marking_independent.py': 'code/62-audit247-code-check_marking_independent.py',
                 'code/verify.py': 'code/62-audit247-code-verify.py',
                 'exploration/README.md': '62-audit247-exploration-README.md',
                 'exploration/boot_search.cpp': 'code/62-audit247-exploration-boot_search.cpp',
                 'licenses/LICENSE.ProveIt': 'data/62-audit247-licenses-LICENSE.ProveIt',
                 'licenses/LICENSE.Wade': 'data/62-audit247-licenses-LICENSE.Wade',
                 'machine/renumbering.json': 'data/62-audit247-machine-renumbering.json',
                 'machine/zfc_prefix247.tm': 'data/62-audit247-machine-zfc_prefix247.tm',
                 'machine/zfc_prefix247_old.tm': 'data/62-audit247-machine-zfc_prefix247_old.tm',
                 'reference/Prog254.v': 'code/62-audit247-reference-Prog254.v',
                 'reference/baseline252_old.tm': 'data/62-audit247-reference-baseline252_old.tm',
                 'reference/lean/Bisim254.lean': 'code/62-audit247-reference-lean-Bisim254.lean',
                 'reference/lean/ChoiceCalibration254.lean': 'code/62-audit247-reference-lean-ChoiceCalibration254.lean',
                 'reference/lean/DirtyProgram254.lean': 'code/62-audit247-reference-lean-DirtyProgram254.lean',
                 'reference/lean/L2Lib254.lean': 'code/62-audit247-reference-lean-L2Lib254.lean',
                 'reference/lean/NativeTheory254.lean': 'code/62-audit247-reference-lean-NativeTheory254.lean',
                 'reference/lean/Prog254.lean': 'code/62-audit247-reference-lean-Prog254.lean',
                 'reference/lean/RegisterPath.lean': 'code/62-audit247-reference-lean-RegisterPath.lean',
                 'reference/lean/RegisterPathClean.lean': 'code/62-audit247-reference-lean-RegisterPathClean.lean',
                 'reference/lean/SiteCoverage.lean': 'code/62-audit247-reference-lean-SiteCoverage.lean',
                 'reference/lean/WFTheory.lean': 'code/62-audit247-reference-lean-WFTheory.lean',
                 'reference/prefix250_old.tm': 'data/62-audit247-reference-prefix250_old.tm',
                 'reference/prior/affine_engine250.py': 'code/62-audit247-reference-prior-affine_engine250.py',
                 'reference/prior/check_macro_inductions250.py': 'code/62-audit247-reference-prior-check_macro_inductions250.py',
                 'reference/prior/prefix250-audit-README.md': '62-audit247-reference-prior-prefix250-audit-README.md',
                 'reference/prior/prefix250-audit-provenance.json': 'data/62-audit247-reference-prior-prefix250-audit-provenance.json',
                 'reference/upstream-attribution.md': '62-audit247-reference-upstream-attribution.md',
                 'results/all_symbolic_instructions.log': 'data/62-audit247-results-all_symbolic_instructions.txt',
                 'results/bootstrap-canonical.json': 'data/62-audit247-results-bootstrap-canonical.json',
                 'results/bootstrap-independent.json': 'data/62-audit247-results-bootstrap-independent.json',
                 'results/bootstrap-search.json': 'data/62-audit247-results-bootstrap-search.json',
                 'results/canonical_sparse_bootstrap.log': 'data/62-audit247-results-canonical_sparse_bootstrap.txt',
                 'results/independent-proof-review.md': '62-audit247-results-independent-proof-review.md',
                 'results/independent_dense_bootstrap.log': 'data/62-audit247-results-independent_dense_bootstrap.txt',
                 'results/independent_literal_instructions.log': 'data/62-audit247-results-independent_literal_instructions.txt',
                 'results/independent_marking.log': 'data/62-audit247-results-independent_marking.txt',
                 'results/instructions.json': 'data/62-audit247-results-instructions.json',
                 'results/literal-instructions.json': 'data/62-audit247-results-literal-instructions.json',
                 'results/logical-review.json': 'data/62-audit247-results-logical-review.json',
                 'results/macro-inductions.json': 'data/62-audit247-results-macro-inductions.json',
                 'results/marking-independent.json': 'data/62-audit247-results-marking-independent.json',
                 'results/pdf-review.json': 'data/62-audit247-results-pdf-review.json',
                 'results/rebuild.json': 'data/62-audit247-results-rebuild.json',
                 'results/reconstruction.log': 'data/62-audit247-results-reconstruction.txt',
                 'results/regeneration-and-portability.json': 'data/62-audit247-results-regeneration-and-portability.json',
                 'results/universal_macro_inductions.log': 'data/62-audit247-results-universal_macro_inductions.txt',
                 'results/verification.json': 'data/62-audit247-results-verification.json'}},
 63: {'slug': 'context246',
      'archive': 'docs/incoming/zfc-context246-20261018.zip',
      'arrival': '8cdc55ff9281b0aaba49bf74b0b225d57f12b893',
      'root': 'zfc-context246',
      'files': ['Makefile',
                'NOTICE.txt',
                'PROVENANCE.json',
                'README.md',
                'SHA256SUMS',
                'code/check_bootstrap.py',
                'code/check_folds.py',
                'code/check_hashes.py',
                'code/check_literal_instructions.py',
                'code/check_local_contracts.py',
                'code/check_macro_inductions.py',
                'code/check_prefix_boxes.py',
                'code/independent_rebuild.py',
                'code/rebuild_machines.py',
                'code/render_table.py',
                'code/review_affine_source.py',
                'code/verify_all.py',
                'machine/renumbering.json',
                'machine/transition-table.tex',
                'machine/zfc_prefix246.tm',
                'machine/zfc_prefix246_old.tm',
                'report.pdf',
                'report.tex',
                'results/affine-source-review.json',
                'results/bootstrap.json',
                'results/contextual-folds.json',
                'results/independent-bootstrap.json',
                'results/independent-rebuild.json',
                'results/independent-theory-audit.json',
                'results/instruction-sites.json',
                'results/literal-instructions.json',
                'results/literal-local-contracts.json',
                'results/macro-inductions.json',
                'results/pdf-build.log',
                'results/pdf-quality.json',
                'results/prefix-box-regression.json',
                'results/rebuild.json',
                'results/source-identity.json',
                'results/verification-summary.json',
                'reviews/README.md',
                'reviews/audit246-results.json',
                'reviews/audit246.py',
                'reviews/independent-calibration.tex',
                'reviews/independent-fold-proof.tex',
                'reviews/portable-audit-notes.md',
                'reviews/prior250/ATTRIBUTION.md',
                'reviews/prior250/code/affine_engine.py',
                'reviews/prior250/code/check_instructions.py',
                'reviews/prior250/code/check_macro_inductions.py',
                'reviews/prior250/code/rebuild_machines.py',
                'reviews/prior250/licenses/LICENSE.ProveIt',
                'reviews/prior250/licenses/LICENSE.Wade',
                'reviews/prior250/sources/Prog254.v',
                'reviews/prior250/sources/baseline252_old.tm',
                'search/README.md',
                'search/seed_search.cpp',
                'sources/LICENSE.ProveIt',
                'sources/Prog254.v',
                'sources/README.upstream-attribution.md',
                'sources/baseline252_old.tm',
                'sources/instruction-sites-physical.json',
                'sources/lean/BinaryPerm252.lean',
                'sources/lean/BinaryZFC252.lean',
                'sources/lean/Bisim254.lean',
                'sources/lean/ChoiceCalibration254.lean',
                'sources/lean/Code254.lean',
                'sources/lean/Code254Proof.lean',
                'sources/lean/ConstructibleAbs.lean',
                'sources/lean/ConstructibleChoice.lean',
                'sources/lean/ConstructibleOrder.lean',
                'sources/lean/ConstructibleZF.lean',
                'sources/lean/DirtyProgram254.lean',
                'sources/lean/DirtyRoot254.lean',
                'sources/lean/Enum254.lean',
                'sources/lean/EnumSafeStart254.lean',
                'sources/lean/L2Lib254.lean',
                'sources/lean/NativeTheory254.lean',
                'sources/lean/Permutation252Frame.lean',
                'sources/lean/Permutation252Simulation.lean',
                'sources/lean/QuotientZF0.lean',
                'sources/lean/RMEquiv254.lean',
                'sources/lean/RegisterBisimulation.lean',
                'sources/lean/RegisterMarkPerm252.lean',
                'sources/lean/RegisterPath.lean',
                'sources/lean/RegisterPathClean.lean',
                'sources/lean/RuntimePerm252.lean',
                'sources/lean/SiteCoverage.lean',
                'sources/lean/WFModel.lean',
                'sources/lean/WFRelativization.lean',
                'sources/lean/WFTheory.lean',
                'sources/lean/WellFoundedPart.lean',
                'sources/lean/ZFNative.lean',
                'sources/lean/ZFRank.lean',
                'sources/lean-snapshot-manifest.json',
                'sources/prefix250_old.tm',
                'sources/prior/NOTICE-prefix250.txt',
                'sources/prior/instruction-sites-physical.json',
                'sources/prior/prefix250-frame-and-calibration.tex',
                'sources/prior/prefix_affine.py',
                'sources/prior/prefix_carry_lemmas.tex',
                'sources/research/candidate-permutation252-README.md',
                'sources/research/choice_calibration254.md',
                'sources/research/dirty_program254.md',
                'sources/research/native_theory254.md',
                'sources/research/permutation252_runtime.md',
                'sources/research/site_coverage.md'],
      'placed': {'Makefile': 'code/63-context246-Makefile',
                 'NOTICE.txt': 'data/63-context246-NOTICE.txt',
                 'PROVENANCE.json': 'data/63-context246-PROVENANCE.json',
                 'SHA256SUMS': 'data/63-context246-SHA256SUMS',
                 'code/check_bootstrap.py': 'code/63-context246-code-check_bootstrap.py',
                 'code/check_folds.py': 'code/63-context246-code-check_folds.py',
                 'code/check_hashes.py': 'code/63-context246-code-check_hashes.py',
                 'code/check_literal_instructions.py': 'code/63-context246-code-check_literal_instructions.py',
                 'code/check_local_contracts.py': 'code/63-context246-code-check_local_contracts.py',
                 'code/check_macro_inductions.py': 'code/63-context246-code-check_macro_inductions.py',
                 'code/check_prefix_boxes.py': 'code/63-context246-code-check_prefix_boxes.py',
                 'code/independent_rebuild.py': 'code/63-context246-code-independent_rebuild.py',
                 'code/rebuild_machines.py': 'code/63-context246-code-rebuild_machines.py',
                 'code/render_table.py': 'code/63-context246-code-render_table.py',
                 'code/review_affine_source.py': 'code/63-context246-code-review_affine_source.py',
                 'code/verify_all.py': 'code/63-context246-code-verify_all.py',
                 'machine/renumbering.json': 'data/63-context246-machine-renumbering.json',
                 'machine/zfc_prefix246.tm': 'data/63-context246-machine-zfc_prefix246.tm',
                 'machine/zfc_prefix246_old.tm': 'data/63-context246-machine-zfc_prefix246_old.tm',
                 'results/affine-source-review.json': 'data/63-context246-results-affine-source-review.json',
                 'results/bootstrap.json': 'data/63-context246-results-bootstrap.json',
                 'results/contextual-folds.json': 'data/63-context246-results-contextual-folds.json',
                 'results/independent-bootstrap.json': 'data/63-context246-results-independent-bootstrap.json',
                 'results/independent-rebuild.json': 'data/63-context246-results-independent-rebuild.json',
                 'results/independent-theory-audit.json': 'data/63-context246-results-independent-theory-audit.json',
                 'results/instruction-sites.json': 'data/63-context246-results-instruction-sites.json',
                 'results/literal-instructions.json': 'data/63-context246-results-literal-instructions.json',
                 'results/literal-local-contracts.json': 'data/63-context246-results-literal-local-contracts.json',
                 'results/macro-inductions.json': 'data/63-context246-results-macro-inductions.json',
                 'results/pdf-build.log': 'data/63-context246-results-pdf-build.txt',
                 'results/pdf-quality.json': 'data/63-context246-results-pdf-quality.json',
                 'results/prefix-box-regression.json': 'data/63-context246-results-prefix-box-regression.json',
                 'results/rebuild.json': 'data/63-context246-results-rebuild.json',
                 'results/source-identity.json': 'data/63-context246-results-source-identity.json',
                 'results/verification-summary.json': 'data/63-context246-results-verification-summary.json',
                 'reviews/README.md': '63-context246-reviews-README.md',
                 'reviews/audit246-results.json': 'data/63-context246-reviews-audit246-results.json',
                 'reviews/audit246.py': 'code/63-context246-reviews-audit246.py',
                 'reviews/portable-audit-notes.md': '63-context246-reviews-portable-audit-notes.md',
                 'reviews/prior250/ATTRIBUTION.md': '63-context246-reviews-prior250-ATTRIBUTION.md',
                 'reviews/prior250/code/affine_engine.py': 'code/63-context246-reviews-prior250-code-affine_engine.py',
                 'reviews/prior250/code/check_instructions.py': 'code/63-context246-reviews-prior250-code-check_instructions.py',
                 'reviews/prior250/code/check_macro_inductions.py': 'code/63-context246-reviews-prior250-code-check_macro_inductions.py',
                 'reviews/prior250/code/rebuild_machines.py': 'code/63-context246-reviews-prior250-code-rebuild_machines.py',
                 'reviews/prior250/licenses/LICENSE.ProveIt': 'data/63-context246-reviews-prior250-licenses-LICENSE.ProveIt',
                 'reviews/prior250/licenses/LICENSE.Wade': 'data/63-context246-reviews-prior250-licenses-LICENSE.Wade',
                 'reviews/prior250/sources/Prog254.v': 'code/63-context246-reviews-prior250-sources-Prog254.v',
                 'reviews/prior250/sources/baseline252_old.tm': 'data/63-context246-reviews-prior250-sources-baseline252_old.tm',
                 'search/README.md': '63-context246-search-README.md',
                 'search/seed_search.cpp': 'code/63-context246-search-seed_search.cpp',
                 'sources/LICENSE.ProveIt': 'data/63-context246-sources-LICENSE.ProveIt',
                 'sources/Prog254.v': 'code/63-context246-sources-Prog254.v',
                 'sources/README.upstream-attribution.md': '63-context246-sources-README.upstream-attribution.md',
                 'sources/baseline252_old.tm': 'data/63-context246-sources-baseline252_old.tm',
                 'sources/instruction-sites-physical.json': 'data/63-context246-sources-instruction-sites-physical.json',
                 'sources/lean/BinaryPerm252.lean': 'code/63-context246-sources-lean-BinaryPerm252.lean',
                 'sources/lean/BinaryZFC252.lean': 'code/63-context246-sources-lean-BinaryZFC252.lean',
                 'sources/lean/Bisim254.lean': 'code/63-context246-sources-lean-Bisim254.lean',
                 'sources/lean/ChoiceCalibration254.lean': 'code/63-context246-sources-lean-ChoiceCalibration254.lean',
                 'sources/lean/Code254.lean': 'code/63-context246-sources-lean-Code254.lean',
                 'sources/lean/Code254Proof.lean': 'code/63-context246-sources-lean-Code254Proof.lean',
                 'sources/lean/ConstructibleAbs.lean': 'code/63-context246-sources-lean-ConstructibleAbs.lean',
                 'sources/lean/ConstructibleChoice.lean': 'code/63-context246-sources-lean-ConstructibleChoice.lean',
                 'sources/lean/ConstructibleOrder.lean': 'code/63-context246-sources-lean-ConstructibleOrder.lean',
                 'sources/lean/ConstructibleZF.lean': 'code/63-context246-sources-lean-ConstructibleZF.lean',
                 'sources/lean/DirtyProgram254.lean': 'code/63-context246-sources-lean-DirtyProgram254.lean',
                 'sources/lean/DirtyRoot254.lean': 'code/63-context246-sources-lean-DirtyRoot254.lean',
                 'sources/lean/Enum254.lean': 'code/63-context246-sources-lean-Enum254.lean',
                 'sources/lean/EnumSafeStart254.lean': 'code/63-context246-sources-lean-EnumSafeStart254.lean',
                 'sources/lean/L2Lib254.lean': 'code/63-context246-sources-lean-L2Lib254.lean',
                 'sources/lean/NativeTheory254.lean': 'code/63-context246-sources-lean-NativeTheory254.lean',
                 'sources/lean/Permutation252Frame.lean': 'code/63-context246-sources-lean-Permutation252Frame.lean',
                 'sources/lean/Permutation252Simulation.lean': 'code/63-context246-sources-lean-Permutation252Simulation.lean',
                 'sources/lean/QuotientZF0.lean': 'code/63-context246-sources-lean-QuotientZF0.lean',
                 'sources/lean/RMEquiv254.lean': 'code/63-context246-sources-lean-RMEquiv254.lean',
                 'sources/lean/RegisterBisimulation.lean': 'code/63-context246-sources-lean-RegisterBisimulation.lean',
                 'sources/lean/RegisterMarkPerm252.lean': 'code/63-context246-sources-lean-RegisterMarkPerm252.lean',
                 'sources/lean/RegisterPath.lean': 'code/63-context246-sources-lean-RegisterPath.lean',
                 'sources/lean/RegisterPathClean.lean': 'code/63-context246-sources-lean-RegisterPathClean.lean',
                 'sources/lean/RuntimePerm252.lean': 'code/63-context246-sources-lean-RuntimePerm252.lean',
                 'sources/lean/SiteCoverage.lean': 'code/63-context246-sources-lean-SiteCoverage.lean',
                 'sources/lean/WFModel.lean': 'code/63-context246-sources-lean-WFModel.lean',
                 'sources/lean/WFRelativization.lean': 'code/63-context246-sources-lean-WFRelativization.lean',
                 'sources/lean/WFTheory.lean': 'code/63-context246-sources-lean-WFTheory.lean',
                 'sources/lean/WellFoundedPart.lean': 'code/63-context246-sources-lean-WellFoundedPart.lean',
                 'sources/lean/ZFNative.lean': 'code/63-context246-sources-lean-ZFNative.lean',
                 'sources/lean/ZFRank.lean': 'code/63-context246-sources-lean-ZFRank.lean',
                 'sources/lean-snapshot-manifest.json': 'data/63-context246-sources-lean-snapshot-manifest.json',
                 'sources/prefix250_old.tm': 'data/63-context246-sources-prefix250_old.tm',
                 'sources/prior/NOTICE-prefix250.txt': 'data/63-context246-sources-prior-NOTICE-prefix250.txt',
                 'sources/prior/instruction-sites-physical.json': 'data/63-context246-sources-prior-instruction-sites-physical.json',
                 'sources/prior/prefix_affine.py': 'code/63-context246-sources-prior-prefix_affine.py',
                 'sources/research/candidate-permutation252-README.md': '63-context246-sources-research-candidate-permutation252-README.md',
                 'sources/research/choice_calibration254.md': '63-context246-sources-research-choice_calibration254.md',
                 'sources/research/dirty_program254.md': '63-context246-sources-research-dirty_program254.md',
                 'sources/research/native_theory254.md': '63-context246-sources-research-native_theory254.md',
                 'sources/research/permutation252_runtime.md': '63-context246-sources-research-permutation252_runtime.md',
                 'sources/research/site_coverage.md': '63-context246-sources-research-site_coverage.md'}}}

def require(condition, message):
    if not condition:
        raise ValueError(message)


def relative_name(name):
    require(isinstance(name, str) and name and "\\" not in name and "\0" not in name,
            f"Invalid relative path: {name!r}")
    p = PurePosixPath(name)
    require(p.parts and not p.is_absolute() and all(x not in (".", "..") for x in p.parts)
            and ":" not in p.parts[0] and p.as_posix() == name.rstrip("/"),
            f"Unsafe archive/map path: {name!r}")
    return p


def archive_members(raw, package):
    archive = zipfile.ZipFile(io.BytesIO(raw))
    files = {}
    seen = set()
    for info in archive.infolist():
        path = relative_name(info.filename)
        require(path.parts[0] == package["root"],
                f"Unexpected archive root: {info.filename}")
        key = path.as_posix()
        require(key not in seen, f"Duplicate archive member: {key}")
        seen.add(key)
        kind = stat.S_IFMT(info.external_attr >> 16)
        require(kind in (0, stat.S_IFREG, stat.S_IFDIR),
                f"Nonregular archive member: {key}")
        require(not info.flag_bits & 1, f"Encrypted archive member: {key}")
        if info.is_dir():
            continue
        require(len(path.parts) > 1 and kind != stat.S_IFDIR,
                f"Invalid file member: {key}")
        relative = PurePosixPath(*path.parts[1:]).as_posix()
        files[relative] = archive.read(info)
    archive.close()
    require(set(files) == set(package["files"]),
            "Archive inventory differs: " + repr(sorted(set(files) ^ set(package["files"]))))
    return files


def verify_placed(repo, package, files):
    for original, placed in package["placed"].items():
        relative_name(original)
        suffix = relative_name(placed)
        path = repo / HOST / str(suffix)
        require(path.is_file() and not path.is_symlink()
                and path.resolve().is_relative_to(repo),
                f"Missing or unsafe placed file: {path}")
        require(path.read_bytes() == files[original],
                f"Placed bytes differ from arrival payload: {path} <- {original}")
    return len(package["placed"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True,
                        help="New, nonexistent directory outside the repository.")
    parser.add_argument("--source", type=int, choices=sorted(PACKAGES),
                        help="Recover one local source; default is both.")
    args = parser.parse_args()
    require(__debug__, "Run without -O.")
    repo = args.repo.resolve(strict=True)
    top = subprocess.run(["git", "-C", str(repo), "rev-parse", "--show-toplevel"],
                         check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         text=True).stdout.strip()
    require(Path(top).resolve() == repo, "--repo must name the Git worktree root.")
    requested_output = args.output.absolute()
    require(not requested_output.exists() and not requested_output.is_symlink(),
            "--output must not already exist, including as a dangling symlink.")
    output = requested_output.resolve()
    require(not output.is_relative_to(repo), "--output must be outside the repository.")
    selected = [args.source] if args.source is not None else sorted(PACKAGES)
    prepared = []
    # Verify all selected inputs before creating any recovery directory.
    for number in selected:
        package = PACKAGES[number]
        reference = package["arrival"] + ":" + package["archive"]
        raw = subprocess.run(["git", "-C", str(repo), "show", reference],
                             check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout
        files = archive_members(raw, package)
        checked = verify_placed(repo, package, files)
        prepared.append((number, package, files, checked))
    output.mkdir(parents=True, exist_ok=False)
    records = []
    for number, package, files, checked in prepared:
        root = output / f"{number}-{package['slug']}" / package["root"]
        for name, payload in files.items():
            target = root.joinpath(*relative_name(name).parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            with target.open("xb") as stream:
                stream.write(payload)
        records.append(dict(source=number, root=str(root), arrival=package["arrival"],
                            archive=package["archive"], recovered_files=len(files),
                            placed_byte_comparisons=checked))
    record = dict(status="RECOVERED_ONLY", packages=records,
                  compiler_invocations=0, test_invocations=0,
                  checksum_manifests_interpreted=False, line_endings_changed=False,
                  note="Archive payloads and placed ancillary files compared directly as bytes; no recorded checksum manifest is parsed or verified.")
    (output / "recovery.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
    for item in records:
        print(f"source {item['source']}: {item['root']}")
    print(f"Recovered {sum(x['recovered_files'] for x in records)} files; "
          f"verified {sum(x['placed_byte_comparisons'] for x in records)} placed byte pairs.")
    print(f"Recovery record: {output / 'recovery.json'}")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, zipfile.BadZipFile, subprocess.CalledProcessError) as error:
        print(f"Recovery failed: {error}", file=sys.stderr)
        raise SystemExit(1)
