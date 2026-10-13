"""Bind the whole-call prefix and coordinate-factor evidence checkpoint.

Only retained evidence, byte maps and arithmetic summaries are checked here.
No LP, recognition discovery, tests, timing, certificate replay subprocess or
PDF build is run.  Execute only after both separate replays and all final
three-pass build artifacts exist.  Historical publication mains are unused.
"""
import ast
from hashlib import sha256
import json
from pathlib import Path
import re

from strict_pachner32_publication import included_tex, python_dependencies
import prepared_euler_matrix_evidence_publication as previous

DATA = Path(__file__).resolve().parent
ROOT = DATA.parent.parent
PREFIX = 'prefix-factor-evidence'
REVISION = '4d1f76f061ac961ee75c4d7d8b067b5fa0ac30f7'
HISTORICAL_MANIFEST = DATA/'prepared-euler-evidence-publication.json'
HISTORICAL_SHA256 = 'e05026d786460203c084123f455f0d75340b7c6284db0b819e092925dfd5902c'
DOCUMENT_EXCEPTIONS = frozenset(('fast/README.md', 'synthesis/README.md',
    'synthesis/report.tex', 'synthesis/marked_cut_handlebodies.tex', 'synthesis/report.pdf'))
CASE_IDS = ('circle', 'trefoil', 'figure_eight', 'TT', 'T25', 'T27', 'W34')
TETRAHEDRA = (7, 10, 16, 11, 17, 31)
ARMS = ('prepared_bland', 'prepared_dantzig_lex')
OPTIONS = dict(max_sectors=256, max_bases=10000, max_crushes=None,
    sector_order='diversified', sector_quantum=64, sector_method='transversal',
    max_pivots=10000, max_anchors=10000, lp_strategy='envelope',
    reduce_vertices=True, unlayer_boundary=True, reduce_pachner32=True,
    reduce_pachner_descent=True, pachner_descent_method='geometric',
    max_tree_nodes=256, tree_model='source', max_hitting_subsets=10000,
    transversal_candidate_policy='conflicts', lp_policy='polynomial',
    lp_fast_path_pivots=None, max_ellipsoid_iterations=10000,
    max_feasibility_calls=10000)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def same(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(same(a[k], b[k]) for k in a)
    if type(a) in (tuple, list):
        return len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
    return a == b


def equal(a, b, message):
    require(same(a, b), message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def value_digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def load(path):
    return json.loads(path.read_bytes())


def natural(value):
    return type(value) is int and value >= 0


def pinned_paths(pins):
    require(type(pins) is dict, 'literal source map')
    paths = set()
    for name, expected in pins.items():
        require(type(name) is str and type(expected) is str and
                re.fullmatch('[0-9a-f]{64}', expected), 'literal SHA-256 pin')
        path = (ROOT/name).resolve()
        require(path.is_relative_to(ROOT) and path.is_file(), 'missing or escaping source pin')
        require(digest(path) == expected, 'changed pinned dependency: '+name)
        paths.add(path)
    return paths


def historical_checkpoint():
    require(digest(HISTORICAL_MANIFEST) == HISTORICAL_SHA256, 'prior 938-file manifest bytes')
    raw = previous.differential.git('show', REVISION+':'+previous.differential.PREFIX+
                                    str(HISTORICAL_MANIFEST.relative_to(ROOT)))
    require(sha256(raw).hexdigest() == HISTORICAL_SHA256, 'prior manifest is committed at source revision')
    manifest = load(HISTORICAL_MANIFEST)
    equal({k: manifest[k] for k in ('schema', 'passed', 'tests', 'test_modules',
        'skipped_tests', 'tested_files', 'general_quasipolynomial', 'new_timing_claims')},
        dict(schema='prepared-euler-evidence-publication-v1', passed=True,
             tests=394, test_modules=44, skipped_tests=0, tested_files=361,
             general_quasipolynomial=False, new_timing_claims=False), 'prior checkpoint scope')
    log = DATA/'prepared-euler-evidence-publication.txt'
    equal(load(log), {k: v for k, v in manifest.items() if k != 'files_sha256'},
          'historical publication stdout binding')
    pins = manifest['files_sha256']
    require(type(pins) is dict and len(pins) == 938, 'prior complete 938-file inventory')
    require(DOCUMENT_EXCEPTIONS <= pins.keys(), 'explicit documentary exceptions are prior files')
    unchanged = {k: v for k, v in pins.items() if k not in DOCUMENT_EXCEPTIONS}
    paths = pinned_paths(unchanged)
    changed = []
    for name in sorted(DOCUMENT_EXCEPTIONS):
        path = ROOT/name
        require(path.is_file(), 'retained documentary file')
        paths.add(path)
        if digest(path) != pins[name]:
            changed.append(name)
    return manifest, dict(revision=REVISION, manifest_sha256=HISTORICAL_SHA256,
        historical_files=938, unchanged_files=len(unchanged),
        allowed_document_changes=sorted(DOCUMENT_EXCEPTIONS), actual_document_changes=changed), \
        paths | {HISTORICAL_MANIFEST, DATA/'prepared-euler-evidence-publication.txt'}


def archive_inventory(payloads):
    return {name: dict(bytes=len(raw), sha256=sha256(raw).hexdigest())
            for name, raw in sorted(payloads.items())}



def coordinate_preflight_failure():
    hashes = {
        'coordinate-factor-replay-first-source.py':
            'd245836c82163297dc6f7c1b64b71cf309d2e3d3391f6e96a9b0990635c6ab9c',
        'coordinate-factor-replay-first-result.json':
            'ac4db1abf6f9829d86688762fafdb23b1302bde1509dc9dc60cf5e7b2b19959d',
        'coordinate-factor-replay-first-output.txt':
            'fa6938999d4dfc2a0365f0f52cf8e7f5708545c9225b97071c3ce54e612da222',
    }
    # Preserve the actual preflight, including its original failed source.
    paths = {DATA/name for name in hashes}
    for path in paths:
        require(digest(path) == hashes[path.name], 'retained coordinate preflight artifact bytes')
    failed = load(DATA/'coordinate-factor-replay-first-result.json')
    equal(failed['passed'], False, 'retained preflight failed honestly')
    equal(failed['phase'], 'archive_validation', 'failure preceded mathematical replay')
    equal(failed['schema'], 'coordinate-factor-portable-replay-v1', 'retained failed replay schema')
    require(len(failed['errors']) == 1 and failed['errors'][0]['type'] == 'CalledProcessError' and
            "'git', 'archive'" in failed['errors'][0]['message'] and
            'exit status 128' in failed['errors'][0]['message'], 'historical git path preflight failure')
    output = (DATA/'coordinate-factor-replay-first-output.txt').read_text()
    require("fatal: pathspec 'Topology/UnknotRecognition/fast/fastunknot' did not match any files" in output,
            'retained exact git path failure log')
    old = (DATA/'coordinate-factor-replay-first-source.py').read_text()
    old_fragment = "    raw=subprocess.check_output(['git','archive','--format=tar',REVISION,\n" \
        "        GIT_PREFIX+'fast/fastunknot',GIT_PREFIX+audit_name],cwd=ROOT)"
    new_fragment = "    repository_root=subprocess.check_output(['git','rev-parse','--show-toplevel'],cwd=ROOT,text=True).strip()\n" \
        "    raw=subprocess.check_output(['git','archive','--format=tar',REVISION,\n" \
        "        GIT_PREFIX+'fast/fastunknot',GIT_PREFIX+audit_name],cwd=repository_root)"
    require(old.count(old_fragment) == 1 and old.replace(old_fragment, new_fragment) ==
            (DATA/'coordinate_factor_replay.py').read_text(), 'sole preflight repair is repository-root cwd')
    return dict(kind='git_archive_path_preflight', preserved=True, mathematical_replay_started=False,
        algorithm_failure=False, native_changes=False, repair='resolve_repository_root_for_git_archive'), paths


def check_coordinate_record():
    """Hash/archive validation only; coordinate_factor_replay.check is not called."""
    import coordinate_factor_replay as factor
    path = DATA/'coordinate-factor-replay.json'
    stdout = DATA/'coordinate-factor-replay.txt'
    helper = DATA/'coordinate_factor_replay.py'
    record = load(path)
    equal(record['schema'], 'coordinate-factor-portable-replay-v1', 'factor replay schema')
    equal(record['passed'], True, 'factor replay success')
    equal(record['phase'], 'complete', 'factor replay complete')
    equal(record['errors'], [], 'factor replay no errors')
    equal(record['coverage'], dict(authenticated_chains=7, terminal_sources=1,
        full_q_matrices=6, singleton_masks=276), 'exact factor replay coverage')
    equal(record['historical_revision'], REVISION, 'factor historical discovery revision')
    equal(record['historical_native_files_authenticated'], 299, 'factor historical native count')
    equal(record['historical_dependency_pins_authenticated'], 301, 'factor historical dependency count')
    equal(record['archive_member_count'], 12, 'factor archive members')
    equal(record['archive_member_bytes'], 5971876, 'factor archive raw bytes')
    require(record['archive_sha256'] == digest(factor.ARCHIVE) == factor.ARCHIVE_SHA256,
            'factor archive digest')
    payloads, manifest = factor.archive_members()  # No execution or extraction.
    equal(manifest['archive_bytes'], 319368, 'factor archive compressed bytes')
    equal(record['current_source_sha256'], factor.current_pins(), 'factor executed replay inputs')
    files = pinned_paths(record['current_source_sha256'])
    full = json.loads(payloads['full/probe.json'])
    singleton = json.loads(payloads['singleton/probe.json'])
    equal(record['full_summary'], full['summary'], 'factor full saved summary binding')
    equal(record['singleton_summary'], singleton['summary'], 'factor mask saved summary binding')
    require(len(record['full_summary']) == 7 and len(record['singleton_summary']) == 6,
            'factor source coverage')
    equal(record['full_summary'][0], dict(id='circle', source_sha256=None, terminal=True),
          'terminal circle has no matrix')
    table = []
    for name, t, row, masks in zip(CASE_IDS[1:], TETRAHEDRA,
            record['full_summary'][1:], record['singleton_summary']):
        expected = dict(id=name, terminal=False, tetrahedra=t, rank=t-1,
            nullity=2*t+1, component_count=1, nonnegative_capable_component_count=1,
            nontrivial_component_count=1, component_tetrahedron_counts=[t],
            zero_columns_free_loops=[], forced_zero_columns_coloops=[])
        equal({key: row[key] for key in expected}, expected, 'full matrix no-split conclusion')
        expected_mask = dict(id=name, source_sha256=row['source_sha256'],
            original_columns=3*t, original_tetrahedra=t, retained_columns_per_mask=3*t-2,
            best_worst_case_size=3*t-2, best_tetrahedra=list(range(t)),
            reduction_from_original_columns=2, reduction_beyond_deleted_competitors=0,
            best_worst_over_original=[3*t-2, 3*t], masks_with_multiple_noncoloop_components=0,
            masks_with_forced_zero_coordinates=0,
            per_tetrahedron=[dict(tetrahedron=i, assignment_largest_component_sizes=[3*t-2]*3,
                                  worst_case_largest_component_size=3*t-2) for i in range(t)])
        equal(masks, expected_mask, 'all retained singleton assignments remain connected')
        table.append(dict(id=name, tetrahedra=t, source_sha256=row['source_sha256'],
            full_columns=3*t, singleton_masks=3*t, remaining_component_columns=3*t-2))
    flags = dict(current_native_geometry_replay=True, current_independent_rank_replay=True,
        archived_mains_executed=False, archived_native_imported=False,
        original_scripts_regenerated=False, lp_queries=0, recognition_discovery=False,
        timings_claimed=False, nonnegative_feasibility_inferred_for_restricted_masks=False,
        general_quasipolynomial=False)
    equal({key: record[key] for key in flags}, flags, 'factor replay scope')
    require(type(record['disabled_discovery_hooks']) is list and record['disabled_discovery_hooks'],
            'factor discovery guard retained')
    # Pure byte/source-table binding; no old matching-witness proof rerun.
    bindings = factor.witness_source_bindings(full)
    equal(record['prior_matching_witness_source_binding'], bindings, 'six literal old-witness source bindings')
    equal(bindings['exact_source_bindings'], 6, 'old matching source count')
    equal(bindings['prior_matching_witnesses'], 276, 'old matching witness count')
    equal(bindings['prior_matching_witnesses_replayed_here'], False, 'no repeated old witness replay')
    equal(bindings['positive_euler_established_by_this_binding'], False, 'no Euler conclusion from matching')
    expected_stdout = {k: v for k, v in record.items() if k not in
        ('current_source_sha256', 'disabled_discovery_hooks', 'singleton_summary')}
    equal(load(stdout), expected_stdout, 'factor replay stdout binding')
    return dict(coverage=record['coverage'], table=table,
        matching_witness_source_bindings=6, prior_matching_witnesses=276,
        saved_replay_sha256=digest(path), archive_sha256=digest(factor.ARCHIVE),
        replay_executed_by_this_helper=False, full_or_singleton_factor_split_found=False,
        general_separator_lower_bound_claimed=False), \
        files | {path, stdout, helper, factor.ARCHIVE, factor.MANIFEST}


def check_whole_call_record():
    """Bind the separately executed archived replay, without starting a child."""
    import whole_call_prefix_replay as pilot
    archive = DATA/'whole-call-prefix-4d1f76f06.tar.gz'
    path = DATA/'whole-call-prefix-replay.json'
    stdout = DATA/'whole-call-prefix-replay.txt'
    helper = DATA/'whole_call_prefix_replay.py'
    record = load(path)
    equal(record['schema'], 'whole-call-prefix-archive-replay-v1', 'whole-call replay schema')
    equal(record['passed'], True, 'whole-call replay success')
    equal(record['phase'], 'complete', 'whole-call replay complete')
    equal(record['failures'], [], 'whole-call replay no failures')
    equal(record['snapshot_revision'], REVISION, 'whole-call source revision')
    equal(record['snapshot_manifest_sha256'], pilot.SNAPSHOT_MANIFEST_SHA256,
          'whole-call frozen manifest')
    require(record['archive']['sha256'] == digest(archive) == pilot.ARCHIVE_SHA256,
            'whole-call immutable archive digest')
    equal(record['archive']['bytes'], archive.stat().st_size, 'whole-call archive size')
    require(Path(record['archive']['path']).name == archive.name, 'whole-call archive path')
    require(record['replay_helper_sha256'] == digest(helper), 'whole-call executed replay code')
    payloads = pilot.checked_members(archive)  # Only hashes and safe inventory validation.
    equal(record['archive_members'], archive_inventory(payloads), 'all whole-call archived bytes')
    equal(record['member_count'], len(payloads), 'whole-call member count')
    equal(record['member_bytes'], sum(map(len, payloads.values())), 'whole-call raw bytes')
    equal(record['returned_summary'], pilot.EXPECTED_RETURNED, 'whole-call exact replay summary')
    expected_coverage = dict(polynomial_control_cases=22, legacy_control_cases=10,
        nested_control_cases=96, callback_arms=2, invalid_control_cases=8,
        diagrams=7, whole_calls=14, arms=2)
    equal(record['coverage'], expected_coverage, 'exact whole-call controls and call coverage')
    equal(pilot.COVERAGE, expected_coverage, 'whole-call helper frozen coverage')
    equal(record['subprocess']['returncode'], 0, 'literal successful whole-call replay exit')
    require(record['subprocess']['stdout_sha256'] == digest(stdout), 'whole-call replay stdout bytes')
    require(record['subprocess']['stderr_sha256'] == sha256(b'').hexdigest(), 'empty replay stderr')
    equal(load(stdout), record['returned_summary'], 'whole-call replay output binding')
    command = record['command']
    require(type(command) is list and len(command) == 9 and all(type(v) is str for v in command),
            'literal isolated whole-call replay command')
    equal(command[1:3], ['-B', '-S'], 'isolated replay Python flags')
    equal(command[4:6], ['check', '--controls'], 'replay entry point, not discovery')
    equal(command[7], '--audit', 'retained audit argument')
    replay_root = Path(command[3]).parent
    require(Path(command[3]).name == 'runner.py' and replay_root.name == pilot.PREFIX.rstrip('/'),
            'archived replay entry point')
    for index, name in ((6, 'controls.json'), (8, 'audit.json')):
        equal(Path(command[index]), replay_root/name, 'exact archived replay input')
    snapshot = json.loads(payloads[pilot.PREFIX+'snapshot/manifest.json'])
    native = {name[len('native/'):]: value for name, value in snapshot['files'].items()
              if name.startswith('native/fastunknot/') and name.endswith('.py')}
    current = {name[len('fast/'):]: value for name, value in previous.differential.native_hashes().items()}
    equal(native, current, 'all archived native Python equals current tested code')
    audit = json.loads(payloads[pilot.PREFIX+'audit.json'])
    controls = json.loads(payloads[pilot.PREFIX+'controls.json'])
    equal(audit['schema'], 'whole-call-prefix-audit-v1', 'whole-call audit schema')
    for document in (audit, controls):
        equal(document['passed'], True, 'all retained pilot phases passed')
        equal(document['failures'], [], 'all retained pilot phases have no failure')
        equal(document['active'], None, 'no unreturned operation')
        equal(document['wall_limit_seconds'], None, 'no external wall cutoff')
        equal(document['timings_claimed'], False, 'no pilot timing claim')
        equal(document['general_quasipolynomial_claimed'], False, 'no general bound claim')
    require(audit['controls_sha256'] == sha256(payloads[pilot.PREFIX+'controls.json']).hexdigest(),
            'whole-call original control input bytes')
    summaries = pilot.call_summaries(audit)
    equal(record['call_summaries'], summaries, 'full retained work/source summaries')
    require(value_digest(summaries) == pilot.EXPECTED_CALL_SUMMARIES_SHA256,
            'frozen complete call-summary digest')
    equal(record['comparisons'], audit['comparisons'], 'saved independently replayed source comparisons')
    equal(record['comparisons'], pilot.EXPECTED_COMPARISONS, 'frozen exact source comparisons')
    calls = audit['calls']
    require(type(calls) is list and len(calls) == 14, 'fourteen retained whole calls')
    rows = []
    for slot, (case_id, arm) in zip(calls, [(name, arm) for name in CASE_IDS for arm in ARMS]):
        equal((slot['case_id'], slot['arm']), (case_id, arm), 'fixed whole-call case/arm order')
        equal(slot['options'], OPTIONS, 'identical complete whole-call controls')
        equal(slot['completion'], 'RETURNED', 'whole call actually returned')
        equal(slot['active_phase'], None, 'no active phase at completion')
        result = slot['result']; stats = result['stats']
        require(slot['result_sha256'] == value_digest(result), 'retained full result digest')
        require(result['status'] in ('UNKNOT', 'KNOTTED', 'INCONCLUSIVE'), 'explicit complete or partial outcome')
        keys = ('lp_calls', 'lp_pivots', 'lp_tableau_updates', 'nodes_attempted',
                'lp_fallbacks', 'lp_ellipsoid_iterations', 'lp_feasibility_calls')
        require(all(natural(stats[key]) for key in keys), 'literal whole-call counters')
        require(stats['lp_pivots'] <= 10000 and stats['nodes_attempted'] <= 256 and
                stats['lp_ellipsoid_iterations'] <= 10000 and stats['lp_feasibility_calls'] <= 10000,
                'whole-call cumulative caps')
        require(all(query['returned'] is True for query in slot['queries']), 'all invoked LP calls returned')
        equal(len(slot['queries']), stats['lp_calls'], 'retained LP query coverage')
        for local, total in (('pivots', 'lp_pivots'), ('tableau_updates', 'lp_tableau_updates'),
                             ('ellipsoid_iterations', 'lp_ellipsoid_iterations'),
                             ('feasibility_calls', 'lp_feasibility_calls')):
            values = [query['result']['stats'][local] for query in slot['queries']]
            require(all(natural(v) for v in values), 'literal returned-query counters')
            equal(sum(values), stats[total], 'returned-query cumulative '+total)
        rows.append(dict(id=case_id, arm=arm, status=result['status'],
            queries=stats['lp_calls'], pivots=stats['lp_pivots'],
            tableau_updates=stats['lp_tableau_updates'], nodes=stats['nodes_attempted'],
            fallbacks=stats['lp_fallbacks'], endpoint=slot['replay']['endpoint']))
    require(len(audit['comparisons']) == 7, 'seven separately compared source paths')
    for name, comparison in zip(CASE_IDS, audit['comparisons']):
        equal(comparison['case_id'], name, 'comparison source order')
        equal(comparison['h_transport_claimed'], False, 'no parameter transport between changed sources')
    flags = dict(discovery_disabled=True, current_native_imported=False,
        archived_native_snapshot_only=True, timings_claimed=False,
        whole_call_shared_budget_claimed=True, general_quasipolynomial_claimed=False)
    equal({k: record[k] for k in flags}, flags, 'whole-call replay scope')
    return dict(coverage=record['coverage'], returned_summary=record['returned_summary'],
        table=rows, source_comparisons=audit['comparisons'],
        archive_sha256=digest(archive), saved_replay_sha256=digest(path),
        replay_subprocess_run_here=False, fresh_whole_calls_run_here=False,
        maintained_native_policy_changed=False, timings_claimed=False,
        whole_call_shared_budget_claimed=True, h_transport_claimed=False), \
        {archive, helper, path, stdout}


def check_builds(historical):
    baseline = DATA/'prepared-euler-evidence-latex-3.txt'
    require(digest(baseline) == historical['files_sha256'][str(baseline.relative_to(ROOT))],
            'authenticated prior diagnostic baseline')
    builds = [DATA/f'{PREFIX}-latex-{i}.txt' for i in (1, 2, 3)]
    for path in builds:
        text = path.read_text()
        require('Output written on report.pdf' in text, 'completed final build pass')
        require(not re.search(r'^!|Emergency stop|Fatal error occurred', text, re.M), 'no fatal TeX errors')
    final = builds[-1].read_text()
    require(not re.search(r'undefined references|undefined on input|Rerun to get|'
                          r'Label\(s\) may have changed|multiply.defined labels', final), 'settled references')
    require(not (previous.core.diagnostics(final)-previous.core.diagnostics(baseline.read_text())),
            'no new warning or box diagnostics relative to authenticated baseline')
    completions = re.findall(r'Output written on report\.pdf \((\d+) pages, (\d+) bytes\)', final)
    require(len(completions) == 1, 'one final PDF completion')
    pages, size = map(int, completions[0])
    pdf = ROOT/'synthesis/report.pdf'
    require(pdf.read_bytes().startswith(b'%PDF-') and pdf.stat().st_size == size, 'current PDF build size')
    tex = included_tex(ROOT/'synthesis/report.tex')
    required = {ROOT/'synthesis'/name for name in ('prepared_euler_matrix.tex',
        'capped_pivot_pilot.tex', 'whole_call_prefix.tex', 'euler_coordinate_factors.tex',
        'conditional_type_matching.tex', 'q_zero_pachner_transport.tex')}
    require(required <= tex, 'complete new and referenced article inclusion')
    return dict(report_pages=pages, report_bytes=size, included_tex_files=len(tex)), \
        tex | set(builds) | {pdf, baseline, ROOT/'fast/README.md', ROOT/'synthesis/README.md'}


def data_dependencies(paths):
    """Supplement the fast-package walker with local data-helper imports."""
    found = set(paths)
    pending = [path for path in found if path.suffix == '.py' and path.parent == DATA]
    seen = set()
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        for node in ast.walk(ast.parse(path.read_text(), filename=str(path))):
            names = [a.name for a in node.names] if isinstance(node, ast.Import) else \
                [node.module] if isinstance(node, ast.ImportFrom) and not node.level and node.module else []
            for name in names:
                local = DATA/(name.split('.')[0]+'.py')
                if local.is_file() and local not in found:
                    found.add(local); pending.append(local)
    return python_dependencies(found)


def main():
    if not __debug__:
        raise RuntimeError('publication binding requires assertions enabled')
    historical, history, files = historical_checkpoint()
    _, tested, more = previous.check_core()  # Pure retained test/source binding only.
    files |= more | {ROOT/name for name in tested}
    whole, more = check_whole_call_record(); files |= more
    factors, more = check_coordinate_record(); files |= more
    preflight, more = coordinate_preflight_failure(); files |= more
    builds, more = check_builds(historical); files |= more
    files |= {Path(__file__).resolve(), DATA/'prepared_euler_matrix_evidence_publication.py',
        DATA/'strict_pachner32_publication.py',
        ROOT/'fast/strict_pachner32_research/common.py',
        ROOT/'fast/strict_pachner32_research/check_evidence.py'}
    files = data_dependencies(files)
    require(all(path.is_file() and path.is_relative_to(ROOT) for path in files), 'complete publication file closure')
    equal(previous.core.test_source_files(), tested, 'test/native dependencies unchanged during binding')
    result = dict(schema='prefix-factor-evidence-publication-v1', passed=True,
        tests=394, test_modules=44, skipped_tests=0, tested_files=len(tested), native_modules=299,
        historical_checkpoint=history, whole_call_prefix=whole, coordinate_factors=factors,
        coordinate_replay_preflight=preflight, **builds,
        maintained_native_sources_changed=False, general_quasipolynomial=False, new_timing_claims=False,
        tests_or_build_run_by_this_helper=False, solver_discovery_run_by_this_helper=False,
        certificate_replay_run_by_this_helper=False, replay_subprocess_run_by_this_helper=False,
        retained_separate_replays_authenticated=True,
        files_sha256={str(path.relative_to(ROOT)): digest(path) for path in sorted(files)})
    output = DATA/f'{PREFIX}-publication.json'
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'files_sha256'}, sort_keys=True))


if __name__ == '__main__':
    main()
