#!/usr/bin/env python3
"""Git-only byte/manifest audit of the three corrected batch80 placements.

No recovered code is imported or executed. No extraction or repository write.
"""
import argparse, hashlib, io, json, subprocess, zipfile
from pathlib import Path, PurePosixPath
PLACEMENT = '8a4e647326e8c92f53e222c10e9107b40918a1ff'

PARENT = '37652b3e60a676e119746f5b874147cb4d9e1d2b'

CORRECTED = '4e270aa4648c5fd7e18626507531046715976535'

ORIGINAL = 'aebfa386e44f232be06b546be9fc2f6138ad34f2'

BASE = 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/'

PACKAGES = {'Eager_Tree_Calculus_Research_Package': {'archive': 'docs/incoming/Eager_Tree_Calculus_Research_Package_corrected.zip',
                                          'archive_sha256': '2c053f50027ec632c2773c9d2ec3e2ace9f621eef5c08bebce0ca06c2d0f3dbd',
                                          'mapping': {'21-eager-tree-CORRECTION.md': ['CORRECTION.md'],
                                                      '21-eager-tree-VERIFICATION.md': ['VERIFICATION.md'],
                                                      'code/21-eager-tree-analyze_growth.py': ['code/analyze_growth.py'],
                                                      'code/21-eager-tree-audit_exact_count.py': ['code/audit_exact_count.py'],
                                                      'code/21-eager-tree-build_pdf.py': ['build_pdf.py'],
                                                      'code/21-eager-tree-canonical.py': ['code/canonical.py'],
                                                      'code/21-eager-tree-canonical_overlay_audit.py': ['code/canonical_overlay_audit.py'],
                                                      'code/21-eager-tree-canonical_projected.py': ['code/canonical_projected.py'],
                                                      'code/21-eager-tree-canonical_projected_audit.py': ['code/canonical_projected_audit.py'],
                                                      'code/21-eager-tree-constant_bit_bound.py': ['code/constant_bit_bound.py'],
                                                      'code/21-eager-tree-counter_source.py': ['code/counter_source.py'],
                                                      'code/21-eager-tree-eager_compiler.py': ['code/eager_compiler.py'],
                                                      'code/21-eager-tree-export_shared_macro.py': ['code/export_shared_macro.py'],
                                                      'code/21-eager-tree-independent_audit.py': ['code/independent_audit.py'],
                                                      'code/21-eager-tree-independent_compiler_audit.py': ['code/independent_compiler_audit.py'],
                                                      'code/21-eager-tree-independent_growth_audit.py': ['code/independent_growth_audit.py'],
                                                      'code/21-eager-tree-independent_shared_audit.py': ['code/independent_shared_audit.py'],
                                                      'code/21-eager-tree-reproduce.py': ['reproduce.py'],
                                                      'code/21-eager-tree-shared_compression.py': ['code/shared_compression.py'],
                                                      'code/21-eager-tree-symbolic_audit.py': ['code/symbolic_audit.py'],
                                                      'code/21-eager-tree-test_application_domain.py': ['code/test_application_domain.py'],
                                                      'code/21-eager-tree-tree_kernel.py': ['code/tree_kernel.py'],
                                                      'code/21-eager-tree-verify_packet_assumptions.py': ['code/verify_packet_assumptions.py'],
                                                      'code/21-eager-tree-verify_shared_macro.py': ['code/verify_shared_macro.py'],
                                                      'data/21-eager-tree-audit_exact_count_receipt.json': ['code/audit_exact_count_receipt.json'],
                                                      'data/21-eager-tree-canonical_identity.json': ['code/canonical_identity.json'],
                                                      'data/21-eager-tree-canonical_overlay_receipt.json': ['code/canonical_overlay_receipt.json'],
                                                      'data/21-eager-tree-canonical_projected_audit_receipt.json': ['code/canonical_projected_audit_receipt.json'],
                                                      'data/21-eager-tree-canonical_projected_identity.json': ['code/canonical_projected_identity.json'],
                                                      'data/21-eager-tree-canonical_projected_receipt.json': ['code/canonical_projected_receipt.json'],
                                                      'data/21-eager-tree-canonical_receipt.json': ['code/canonical_receipt.json'],
                                                      'data/21-eager-tree-constant_bit_bound.json': ['code/constant_bit_bound.json'],
                                                      'data/21-eager-tree-counter_source_receipt.json': ['code/counter_source_receipt.json'],
                                                      'data/21-eager-tree-cyclic_counterfeit.json': ['code/cyclic_counterfeit.json'],
                                                      'data/21-eager-tree-eager_compiler_receipt.json': ['code/eager_compiler_receipt.json'],
                                                      'data/21-eager-tree-exact_growth_receipt.json': ['code/exact_growth_receipt.json'],
                                                      'data/21-eager-tree-identity_certificate.json': ['code/identity_certificate.json'],
                                                      'data/21-eager-tree-independent_compiler_receipt.json': ['code/independent_compiler_receipt.json'],
                                                      'data/21-eager-tree-independent_growth_receipt.json': ['code/independent_growth_receipt.json'],
                                                      'data/21-eager-tree-independent_receipt.json': ['code/independent_receipt.json'],
                                                      'data/21-eager-tree-independent_shared_receipt.json': ['code/independent_shared_receipt.json'],
                                                      'data/21-eager-tree-literal_universal_tree.json': ['code/literal_universal_tree.json'],
                                                      'data/21-eager-tree-literal_universal_tree.sexpr': ['code/literal_universal_tree.sexpr'],
                                                      'data/21-eager-tree-packet_assumptions_receipt.json': ['code/packet_assumptions_receipt.json'],
                                                      'data/21-eager-tree-receipt.json': ['code/receipt.json'],
                                                      'data/21-eager-tree-requirements-optional.txt': ['requirements-optional.txt'],
                                                      'data/21-eager-tree-shared_compression_program.json': ['code/shared_compression_program.json'],
                                                      'data/21-eager-tree-shared_compression_receipt.json': ['code/shared_compression_receipt.json'],
                                                      'data/21-eager-tree-shared_symbolic_proofs.json': ['code/shared_symbolic_proofs.json'],
                                                      'data/21-eager-tree-sources.json': ['sources.json'],
                                                      'data/21-eager-tree-symbolic_receipt.json': ['code/symbolic_receipt.json'],
                                                      'data/21-eager-tree-universal_code_circuit.json': ['code/universal_code_circuit.json'],
                                                      'data/21-eager-tree-universal_lambda_source.json': ['code/universal_lambda_source.json']},
                                          'old_archive': 'docs/incoming/Eager_Tree_Calculus_Research_Package.zip',
                                          'old_archive_sha256': '5c6c100296a58df366939febf2f7b6ca57616f17f77a71520f6f3a5e20204ab4',
                                          'prefix': '21-eager-tree-',
                                          'report': 'canonical-diophantine-certificates',
                                          'root': 'eager-tree-certificates'},
 'Reset_Petri_Net_Certificates': {'archive': 'docs/incoming/Reset_Petri_Net_Certificates_corrected.zip',
                                  'archive_sha256': '8d5b9b1a52c33aeadb8b4200fd9c138bd016f2651ebcfccf1a939e03715486d3',
                                  'mapping': {'17-reset-net-CORRECTION.md': ['CORRECTION.md'],
                                              '17-reset-net-VALIDATION.md': ['VALIDATION.md'],
                                              'code/17-reset-net-budget-audit-audit_budget.py': ['budget-audit/audit_budget.py'],
                                              'code/17-reset-net-build-pdf.sh': ['build-pdf.sh'],
                                              'code/17-reset-net-build_net.py': ['build_net.py'],
                                              'code/17-reset-net-checks-audit.py': ['checks/audit.py'],
                                              'code/17-reset-net-checks-audit_exact_domains.py': ['checks/audit_exact_domains.py'],
                                              'code/17-reset-net-checks-audit_generated_families.py': ['checks/audit_generated_families.py'],
                                              'code/17-reset-net-checks-audit_padding_and_generic_peak.py': ['checks/audit_padding_and_generic_peak.py'],
                                              'code/17-reset-net-peak_quadratic.py': ['peak_quadratic.py'],
                                              'code/17-reset-net-replay_and_verify.py': ['replay_and_verify.py'],
                                              'code/17-reset-net-reset_quadratic.py': ['reset_quadratic.py'],
                                              'code/17-reset-net-run-checks.sh': ['run-checks.sh'],
                                              'code/17-reset-net-shared-checks-audit_prime_macros.py': ['shared-checks/audit_prime_macros.py'],
                                              'code/17-reset-net-shared-checks-audit_shared.py': ['shared-checks/audit_shared.py'],
                                              'code/17-reset-net-shared-reset-arcs-build_shared.py': ['shared-reset-arcs/build_shared.py'],
                                              'code/17-reset-net-source_quadratic.py': ['source_quadratic.py'],
                                              'code/17-reset-net-two-counter-build_variant.py': ['two-counter/build_variant.py'],
                                              'code/17-reset-net-two-counter-verify_source.py': ['two-counter/verify_source.py'],
                                              'code/17-reset-net-two-reset-audit-audit_two_reset.py': ['two-reset-audit/audit_two_reset.py'],
                                              'code/17-reset-net-two-reset-audit-compare_release_net.py': ['two-reset-audit/compare_release_net.py'],
                                              'code/17-reset-net-verify_source.py': ['verify_source.py'],
                                              'data/17-reset-net-SOURCE_PROVENANCE.json': ['SOURCE_PROVENANCE.json'],
                                              'data/17-reset-net-accepting_all_duration_witness_N390.json': ['accepting_all_duration_witness_N390.json'],
                                              'data/17-reset-net-accepting_peak_trace.json': ['accepting_peak_trace.json'],
                                              'data/17-reset-net-accepting_peak_witness.json': ['accepting_peak_witness.json'],
                                              'data/17-reset-net-accepting_reset_trace.json': ['accepting_reset_trace.json'],
                                              'data/17-reset-net-accepting_reset_witness.json': ['accepting_reset_witness.json'],
                                              'data/17-reset-net-budget-audit-audit_results.json': ['budget-audit/audit_results.json'],
                                              'data/17-reset-net-budget-audit-shortest_accepting_word.json': ['budget-audit/shortest_accepting_word.json'],
                                              'data/17-reset-net-checks-AUDIT_RESULTS.json': ['checks/AUDIT_RESULTS.json'],
                                              'data/17-reset-net-checks-EXACT_DOMAIN_RESULTS.json': ['checks/EXACT_DOMAIN_RESULTS.json'],
                                              'data/17-reset-net-checks-GENERATED_FAMILIES_RESULTS.json': ['checks/GENERATED_FAMILIES_RESULTS.json'],
                                              'data/17-reset-net-checks-PADDING_AND_GENERIC_PEAK_RESULTS.json': ['checks/PADDING_AND_GENERIC_PEAK_RESULTS.json'],
                                              'data/17-reset-net-checks-PORTABILITY_RESULTS.json': ['checks/PORTABILITY_RESULTS.json'],
                                              'data/17-reset-net-net_ledger.json': ['net_ledger.json'],
                                              'data/17-reset-net-reset_net.json': ['reset_net.json'],
                                              'data/17-reset-net-shared-checks-audit_receipt.json': ['shared-checks/audit_receipt.json'],
                                              'data/17-reset-net-shared-checks-independent_A64_macro_trace.json': ['shared-checks/independent_A64_macro_trace.json'],
                                              'data/17-reset-net-shared-checks-prime_macro_receipt.json': ['shared-checks/prime_macro_receipt.json'],
                                              'data/17-reset-net-shared-reset-arcs-three-counter-accepting_peak_witness_N446.json': ['shared-reset-arcs/three-counter/accepting_peak_witness_N446.json'],
                                              'data/17-reset-net-shared-reset-arcs-three-counter-accepting_reset_trace_N446.json': ['shared-reset-arcs/three-counter/accepting_reset_trace_N446.json'],
                                              'data/17-reset-net-shared-reset-arcs-three-counter-net_ledger.json': ['shared-reset-arcs/three-counter/net_ledger.json'],
                                              'data/17-reset-net-shared-reset-arcs-two-counter-accepting_macro_count_A64.json': ['shared-reset-arcs/two-counter/accepting_macro_count_A64.json'],
                                              'data/17-reset-net-shared-reset-arcs-two-counter-net_ledger.json': ['shared-reset-arcs/two-counter/net_ledger.json'],
                                              'data/17-reset-net-shared-reset-arcs-verification_receipt.json': ['shared-reset-arcs/verification_receipt.json'],
                                              'data/17-reset-net-source_verification_receipt.json': ['source_verification_receipt.json'],
                                              'data/17-reset-net-two-counter-net_ledger.json': ['two-counter/net_ledger.json'],
                                              'data/17-reset-net-two-counter-source-accepting_example.json': ['two-counter/source/accepting_example.json'],
                                              'data/17-reset-net-two-counter-source_verification_receipt.json': ['two-counter/source_verification_receipt.json'],
                                              'data/17-reset-net-two-reset-audit-accepting_macro_trace.json': ['two-reset-audit/accepting_macro_trace.json'],
                                              'data/17-reset-net-two-reset-audit-audit_receipt.json': ['two-reset-audit/audit_receipt.json'],
                                              'data/17-reset-net-two-reset-audit-release_comparison_receipt.json': ['two-reset-audit/release_comparison_receipt.json'],
                                              'data/17-reset-net-verification_receipt.json': ['verification_receipt.json']},
                                  'old_archive': 'docs/incoming/Reset_Petri_Net_Certificates.zip',
                                  'old_archive_sha256': 'b1efbc90aac106061e93ffc92adda686b8e1b9f57539aae976bf227dffec83e3',
                                  'prefix': '17-reset-net-',
                                  'report': 'quadratic-orthant-certificates',
                                  'root': 'reset-net-release'},
 'Sparse_Lattice_Diophantine_Certificates': {'archive': 'docs/incoming/Sparse_Lattice_Diophantine_Certificates_corrected.zip',
                                             'archive_sha256': 'cf9b546baaece745c047f6ce33574d10104f03c9849f4114626a916c1deec1e2',
                                             'mapping': {'13-sparse-lattice-CORRECTION.md': ['CORRECTION.md'],
                                                         '13-sparse-lattice-SOURCE-PROVENANCE.md': ['SOURCE-PROVENANCE.md'],
                                                         'code/13-sparse-lattice-build.sh': ['build.sh'],
                                                         'code/13-sparse-lattice-crosscheck_row_producer.py': ['replay/independent/crosscheck_row_producer.py'],
                                                         'code/13-sparse-lattice-independent_dynamics.py': ['replay/independent/independent_dynamics.py'],
                                                         'code/13-sparse-lattice-independent_polynomial_audit.py': ['replay/independent/independent_polynomial_audit.py'],
                                                         'code/13-sparse-lattice-independent_row_polynomial_audit.py': ['replay/independent/independent_row_polynomial_audit.py'],
                                                         'code/13-sparse-lattice-morita_audit.py': ['replay/core/morita_audit.py',
                                                                                                    'replay/morita/audit.py'],
                                                         'code/13-sparse-lattice-run-replay.sh': ['run-replay.sh'],
                                                         'code/13-sparse-lattice-run_checks.py': ['replay/core/run_checks.py'],
                                                         'code/13-sparse-lattice-run_morita_fixture.py': ['replay/core/run_morita_fixture.py'],
                                                         'code/13-sparse-lattice-run_release.py': ['replay/run_release.py'],
                                                         'code/13-sparse-lattice-semilinearity-audit.py': ['replay/semilinearity/audit.py'],
                                                         'code/13-sparse-lattice-semilinearity-check.py': ['replay/semilinearity/check.py'],
                                                         'code/13-sparse-lattice-sparse_mass.py': ['replay/core/sparse_mass.py'],
                                                         'code/13-sparse-lattice-test_poly_exactness.py': ['replay/core/test_poly_exactness.py'],
                                                         'code/13-sparse-lattice-two-mass-audit.py': ['replay/two-mass/audit.py'],
                                                         'code/13-sparse-lattice-two-mass-regression.py': ['replay/two-mass/regression.py'],
                                                         'data/13-sparse-lattice-binary_three_way_collision.json': ['replay/core/fixtures/binary_three_way_collision.json'],
                                                         'data/13-sparse-lattice-binary_three_way_collision_orthant.json': ['replay/core/fixtures/binary_three_way_collision_orthant.json'],
                                                         'data/13-sparse-lattice-coefficient-crosscheck.json': ['receipts/coefficient-crosscheck.json'],
                                                         'data/13-sparse-lattice-core-checks.json': ['receipts/core-checks.json'],
                                                         'data/13-sparse-lattice-doubling-complete.csv': ['tables/doubling-complete.csv'],
                                                         'data/13-sparse-lattice-false-signal-complete.csv': ['tables/false-signal-complete.csv'],
                                                         'data/13-sparse-lattice-huge_empty_span.json': ['replay/core/fixtures/huge_empty_span.json'],
                                                         'data/13-sparse-lattice-independent-dynamics.json': ['receipts/independent-dynamics.json'],
                                                         'data/13-sparse-lattice-independent-rows.json': ['receipts/independent-rows.json'],
                                                         'data/13-sparse-lattice-legacy-factorized.json': ['receipts/legacy-factorized.json'],
                                                         'data/13-sparse-lattice-morita-n0.json': ['receipts/morita-n0.json'],
                                                         'data/13-sparse-lattice-morita-n2.json': ['receipts/morita-n2.json'],
                                                         'data/13-sparse-lattice-morita-source.json': ['receipts/morita-source.json'],
                                                         'data/13-sparse-lattice-poly-exactness.json': ['receipts/poly-exactness.json'],
                                                         'data/13-sparse-lattice-release-verification.json': ['receipts/release-verification.json'],
                                                         'data/13-sparse-lattice-semilinearity-components.json': ['receipts/semilinearity-components.json'],
                                                         'data/13-sparse-lattice-semilinearity-independent.json': ['receipts/semilinearity-independent.json'],
                                                         'data/13-sparse-lattice-ternary_mixed_mass.json': ['replay/core/fixtures/ternary_mixed_mass.json'],
                                                         'data/13-sparse-lattice-two-mass-arithmetic.json': ['receipts/two-mass-arithmetic.json'],
                                                         'data/13-sparse-lattice-visual-qa.json': ['receipts/visual-qa.json']},
                                             'old_archive': 'docs/incoming/Sparse_Lattice_Diophantine_Certificates.zip',
                                             'old_archive_sha256': '90c9dadeccad7c70c777b141b0c65029b992048fd69448f0f8e035ec522cdc68',
                                             'prefix': '13-sparse-lattice-',
                                             'report': 'signal-machine-collision-certificates',
                                             'root': 'sparse-lattice-release'}}

EXPECTED_CHANGES = [['A',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/21-eager-tree-CORRECTION.md'],
 ['M',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/code/21-eager-tree-reproduce.py'],
 ['A',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/code/21-eager-tree-test_application_domain.py'],
 ['M',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/code/21-eager-tree-tree_kernel.py'],
 ['M',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/data/21-eager-tree-independent_receipt.json'],
 ['M',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/data/21-eager-tree-receipt.json'],
 ['A',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/17-reset-net-CORRECTION.md'],
 ['M',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/code/17-reset-net-build_net.py'],
 ['A',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/code/17-reset-net-checks-audit_exact_domains.py'],
 ['M',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/code/17-reset-net-peak_quadratic.py'],
 ['M',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/code/17-reset-net-run-checks.sh'],
 ['A',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/data/17-reset-net-checks-EXACT_DOMAIN_RESULTS.json'],
 ['M',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/data/17-reset-net-checks-PADDING_AND_GENERIC_PEAK_RESULTS.json'],
 ['A',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/13-sparse-lattice-CORRECTION.md'],
 ['M',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/13-sparse-lattice-SOURCE-PROVENANCE.md'],
 ['M',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/code/13-sparse-lattice-run_release.py'],
 ['M',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/code/13-sparse-lattice-sparse_mass.py'],
 ['A',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/code/13-sparse-lattice-test_poly_exactness.py'],
 ['M',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/data/13-sparse-lattice-coefficient-crosscheck.json'],
 ['A',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/data/13-sparse-lattice-poly-exactness.json'],
 ['M',
  'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/data/13-sparse-lattice-release-verification.json'],
 ['D', 'docs/incoming/Eager_Tree_Calculus_Research_Package_corrected.zip'],
 ['D', 'docs/incoming/Reset_Petri_Net_Certificates_corrected.zip'],
 ['D', 'docs/incoming/Sparse_Lattice_Diophantine_Certificates_corrected.zip']]

UNCHANGED_PRESENTATION = {'SetTheory/Cardinals/.gitattributes': '2226955c34c77cea76c19365987cccaaf8655f7508f4481318455ed968e2128a',
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/README.md': '8df1c7b5cade5b59a37082d8933da72c9af07654f507da94d0cdea64d9e90707',
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.pdf': '050f896b175322cce0d1662827ac0e6f4f207e60d54b2c8a3a1ff9c6ef2cdb11',
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/article.tex': '2bc70d847ea296d59d0686edb42500cdc14ebe39c238ef07960b78534c839069',
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/README.md': '548929d87a89e02a6b97520df68eb17025764caa34353692818b616f6a9a85f1',
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/article.pdf': 'c2bea56002fb0cf717f986764142ad2b077ae835bf17d15491d245d43560eabc',
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates/article.tex': '36cd72be5fb0cf5fe2c06c79af530e2285830bb78c2ce613044b78ae623ddaf3',
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/README.md': 'dc3a5253f2b377eac2d2219229661b389d8cf1498ec6d567bcaa95bcdb7f8f99',
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/article.pdf': 'aa54fea4b203cb6ecb15a76e55dffccec2be928b417e83387b3b1cd80b4df166',
 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/article.tex': '2e1e73628bf21158f4fe63beaf2fd5e13c08259dfea666929081a8f98d1f581a'}
def need(condition, message):
    if not condition:
        raise ValueError(message)

def exact(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(type(k) is str and exact(a[k], b[k]) for k in a)
    if type(a) in (list, tuple):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b

def sha(data):
    return hashlib.sha256(data).hexdigest()

def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args], timeout=60)

def blob(repo, commit, path):
    return git(repo, 'show', commit + ':' + path)

def archive(data, pin, prefix):
    need(sha(data) == pin, 'Pinned archive bytes')
    result = {}
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        infos = z.infolist()
        need(len({i.filename for i in infos}) == len(infos), 'Duplicate archive entries')
        for info in infos:
            p = PurePosixPath(info.filename)
            need(not p.is_absolute() and '..' not in p.parts and '\\' not in info.filename,
                 'Unsafe archive path')
            need(p.parts and p.parts[0] == prefix and len(p.parts) > 1 or
                 (info.is_dir() and p.parts == (prefix,)), 'Wrong archive root')
            need((info.external_attr >> 16) & 0o170000 != 0o120000, 'Archive symlink')
            if info.is_dir():
                continue
            name = str(PurePosixPath(*p.parts[1:]))
            need(prefix + '/' + name == info.filename and name not in result,
                 'Noncanonical/duplicate member path')
            result[name] = z.read(info)
    return result

def manifest(files):
    name = 'MANIFEST.sha256' if 'MANIFEST.sha256' in files else 'SHA256SUMS'
    seen = {}
    for line in files[name].decode().splitlines():
        if not line.strip():
            continue
        digest, path = line.split(maxsplit=1)
        path = path.lstrip('*').removeprefix('./')
        need(path in files and path not in seen and sha(files[path]) == digest,
             'Full original-layout manifest: ' + path)
        seen[path] = digest
    need(set(seen) == set(files) - {name}, 'Manifest exhaustive coverage')
    return dict(file=name, sha256=sha(files[name]), entries=len(seen))

def layout_checks(spec, files, placed_paths):
    report = BASE + spec['report'] + '/'
    # Static path witnesses, not executions of the flattened runners.
    if spec['prefix'] == '21-eager-tree-':
        witnesses = [
            ('reproduce.py', "str(ROOT / 'code' / step)", 'code/code/test_application_domain.py'),
            ('code/test_application_domain.py', "with_name('tree_kernel.py')", 'code/tree_kernel.py'),
        ]
        omitted_helpers = ['verify_manifest.py', 'MANIFEST.sha256']
    elif spec['prefix'] == '17-reset-net-':
        witnesses = [
            ('run-checks.sh', 'python3 build_net.py', 'code/build_net.py'),
            ('checks/audit_exact_domains.py', 'from build_net import fire, initial', 'build_net.py'),
            ('checks/audit_exact_domains.py', "ROOT/'source/virtual3.json'", 'source/virtual3.json'),
        ]
        omitted_helpers = ['verify-manifest.py', 'SHA256SUMS']
    else:
        witnesses = [
            ('replay/run_release.py', "shutil.copytree(ROOT/'replay',code", 'replay'),
            ('replay/core/test_poly_exactness.py', 'import sparse_mass as repaired', 'code/sparse_mass.py'),
            ('replay/core/test_poly_exactness.py', 'fixtures/binary_three_way_collision.json',
             'code/fixtures/binary_three_way_collision.json'),
        ]
        omitted_helpers = ['replay/verify_manifest.py', 'SHA256SUMS', 'replay/package_release.py']
    result = []
    for member, literal, missing in witnesses:
        lines = files[member].decode().splitlines()
        found = [i + 1 for i, line in enumerate(lines) if literal in line]
        need(len(found) == 1, 'Exact runner source witness')
        target = report + missing
        need(target not in placed_paths and not any(p.startswith(target + '/') for p in placed_paths),
             'Known original-layout prerequisite unexpectedly present')
        actual = [report + p for p, members in spec['mapping'].items() if member in members]
        need(len(actual) == 1, 'Unique placed runner')
        result.append(dict(member=member, placed_path=actual[0], line=found[0], literal=literal,
                           missing_path_in_placed_tree=target))
    mapped = {n for names in spec['mapping'].values() for n in names}
    need(all(n in files and n not in mapped for n in omitted_helpers), 'Omitted layout helpers')
    return dict(static_path_witnesses=result, omitted_manifest_and_packaging_helpers=omitted_helpers,
                scope='The prefixed flattened supplements preserve release bytes, not the original runnable layout. '
                      'Restore the pinned archive layout before using release commands. No runner executed here.')

def verify(repo):
    repo = Path(repo)
    for commit in (PLACEMENT, PARENT, CORRECTED, ORIGINAL):
        need(git(repo, 'rev-parse', commit + '^{commit}').decode().strip() == commit, 'Immutable commit identity')
    need(git(repo, 'rev-parse', PLACEMENT + '^').decode().strip() == PARENT, 'Placement parent')
    changes = [line.split('\t') for line in git(repo, 'diff-tree', '--no-commit-id', '--name-status', '-r', PLACEMENT).decode().splitlines()]
    need(exact(changes, EXPECTED_CHANGES), 'Complete placement delta')
    changed_nonzip = {p: status for status, p in changes if not p.endswith('.zip')}
    removed = sorted(p for status, p in changes if status == 'D')
    need(removed == sorted(s['archive'] for s in PACKAGES.values()), 'Exactly three removed archives')
    presentation = []
    for path, pin in UNCHANGED_PRESENTATION.items():
        before, after = blob(repo, PARENT, path), blob(repo, PLACEMENT, path)
        need(before == after and sha(after) == pin, 'Unchanged assembled presentation/attributes')
        presentation.append(dict(path=path, sha256=pin, unchanged_from_parent=True))
    results, consumed, all_aliases = [], set(), []
    for package, spec in PACKAGES.items():
        raw = blob(repo, CORRECTED, spec['archive'])
        need(blob(repo, PARENT, spec['archive']) == raw, 'Removed archive exactly corrected arrival')
        files = archive(raw, spec['archive_sha256'], spec['root'])
        old = archive(blob(repo, ORIGINAL, spec['old_archive']), spec['old_archive_sha256'], spec['root'])
        need(set(old) <= set(files), 'No original member removed')
        report = BASE + spec['report'] + '/'
        all_tree = set(git(repo, 'ls-tree', '-r', '--name-only', PLACEMENT, '--', report).decode().splitlines())
        actual = {p for p in all_tree if PurePosixPath(p).name.startswith(spec['prefix'])}
        expected = {report + p for p in spec['mapping']}
        need(actual == expected, 'Complete package-prefix placement set')
        served, mapping, restored = set(), [], dict(files)
        for relative, members in spec['mapping'].items():
            path = report + relative
            data = blob(repo, PLACEMENT, path)
            need(members and len(set(members)) == len(members), 'Distinct source aliases')
            need(all(n in files and data == files[n] and n not in served for n in members),
                 'Package-qualified exact placed source bytes')
            status = changed_nonzip.get(path, 'unchanged')
            if path in changed_nonzip:
                need(status in ('A', 'M'), 'Only supplemental additions/modifications')
                consumed.add(path)
            if status != 'A':
                previous = blob(repo, PARENT, path)
                need(all(n in old and previous == old[n] for n in members), 'Previous uncorrected placement bytes')
                need((previous != data) == (status == 'M'), 'Changed-member/placement status agrees')
            else:
                need(all(n not in old for n in members), 'New placement is a new corrected member')
            served.update(members)
            for n in members:
                restored[n] = data
            row = dict(placed_path=path, source_members=members, sha256=sha(data), bytes=len(data), status=status)
            mapping.append(row)
            if len(members) > 1:
                all_aliases.append(row)
        need(exact(restored, files), 'Complete in-memory original-layout reconstruction')
        manifest_data = manifest(restored)
        unchanged = {n for n in old if old[n] == files[n]}
        corrected = sorted(n for n in old if old[n] != files[n])
        added = sorted(set(files) - set(old))
        math = sorted(n for n in old if n.endswith(('.tex', '.pdf')))
        need(all(n in unchanged for n in math), 'Original manuscript and PDF unchanged')
        absent = sorted(set(files) - served)
        # No cross-package equal-content file is used to fill these omissions.
        results.append(dict(package=package, archive=spec['archive'], archive_sha256=spec['archive_sha256'],
            original_archive=spec['old_archive'], original_archive_sha256=spec['old_archive_sha256'],
            report=spec['report'], prefix=spec['prefix'], mapping=mapping,
            full_member_pins={n:sha(b) for n,b in sorted(files.items())}, manifest=manifest_data,
            archive_changed_members=corrected, archive_added_members=added,
            unchanged_manuscript_and_PDF_members=math, absent_from_package_placement=absent,
            layout=layout_checks(spec, files, all_tree),
            counts=dict(original_members=len(old), corrected_members=len(files), placed_files=len(mapping),
                served_member_paths=len(served), absent_member_paths=len(absent),
                modified_placed_files=sum(r['status']=='M' for r in mapping),
                added_placed_files=sum(r['status']=='A' for r in mapping),
                unchanged_placed_files=sum(r['status']=='unchanged' for r in mapping),
                unchanged_archive_members=len(unchanged),
                unchanged_served_member_paths=len(unchanged & served),
                unchanged_absent_member_paths=len(unchanged - served)),
            full_original_layout_restoration='All member bytes and all original manifest entries verified in memory; no recovered source executed.'))
    need(consumed == set(changed_nonzip), 'Every changed non-ZIP path authenticated; none unmatched')
    totals = {key:sum(p['counts'][key] for p in results) for key in results[0]['counts']}
    need(totals['placed_files']==145 and totals['served_member_paths']==146 and totals['absent_member_paths']==51,
         'Independent full coverage ledger')
    need(totals['modified_placed_files']==13 and totals['added_placed_files']==8 and len(all_aliases)==1,
         'Independent changed-file/alias ledger')
    return dict(status='PASS_BATCH80_CORRECTED_PLACEMENT',placement_commit=PLACEMENT,parent_commit=PARENT,
        corrected_archive_commit=CORRECTED,original_archive_commit=ORIGINAL,complete_delta=changes,
        counts=totals,removed_corrected_archives=removed,packages=results,same_package_aliases=all_aliases,
        unchanged_presentation=presentation,
        migrated_repairs=[
            'Tree Evaluation.app exact-natural boundary before cache and mutation is now present in the maintained source.',
            'Reset compile_peak Boolean options plus fire/initial exact-natural boundaries are now present in maintained sources.',
            'Sparse Poly exact immutable canonical constructor is now present in the maintained source.'],
        scope='Git-only source-authentication and package-qualified placement audit. No imported or executed package code; '
              'no author suite, fresh theorem/API review, working-tree mutation, or claim that flattened runners are directly executable.')

if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True)
    p.add_argument('--output',type=Path)
    p.add_argument('--expect',type=Path)
    a=p.parse_args(); result=verify(a.repo)
    if a.expect:
        need(exact(result,json.loads(a.expect.read_text())), 'Type-sensitive saved receipt equality')
    if a.output:
        a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status=result['status'],counts=result['counts'],
        packages=[dict(package=q['package'],counts=q['counts']) for q in result['packages']]),indent=2))
