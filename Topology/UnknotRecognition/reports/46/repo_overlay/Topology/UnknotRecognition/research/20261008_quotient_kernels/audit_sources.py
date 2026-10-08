"""Static portability and source-digest audit; never reruns benchmarks or tests.

Run from any directory. Paths in the output are relative to
Topology/UnknotRecognition. This audit checks the overlay-after-application
workflow against the pinned repository, not a standalone overlay checkout.
"""
from __future__ import annotations

import argparse
import ast
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[1]
FAST = PROJECT / 'fast'
BASELINE = '58ee11a97d5fd7f21647c57eefaf3ecc007931d6'
PREFIX = 'Topology/UnknotRecognition/'

BENCHMARKS = {
    'coefficient': ('fast/benchmark_coefficient_span.py',
                    'fast/coefficient_research/results.json', 'source_hashes'),
    'cyclic_overlap': ('fast/cyclic_overlap_research/benchmark.py',
                       'fast/cyclic_overlap_research/results.json', 'source_sha256'),
    'interval': ('fast/interval_research/benchmark.py',
                 'fast/interval_research/results.json', 'source_sha256'),
    'normal_surface': ('fast/normal_orbit_research/benchmark.py',
                       'fast/normal_orbit_research/results.json', 'source_sha256'),
}
TESTS = ['fast/tests/test_coefficient_span.py',
         'fast/tests/test_cyclic_overlap_index.py',
         'fast/tests/test_interval_orbits.py',
         'fast/tests/test_normal_surface_orbits.py']
EXTRA_CHECKED = ['fast/normal_orbit_research/fixtures.py',
                 'fast/cyclic_overlap_research/make_summary.py',
                 'research/20261008_quotient_kernels/render_results.py']
CRITICAL_DEPENDENCIES = [
    'fast/primary_research/families.py',
    'fast/benchmark_compressed_words.py', 'fast/hard_unknots.py',
    'fast/tests/test_compressed_words.py', 'fast/tests/test_relator_overlap.py',
    'fast/tests/test_fastunknot.py', 'fast/normal_research/gordian.json',
    'fast/tests/fixtures/gordian_relator_power.json',
    'fast/normal_orbit_research/fixtures.py',
    'fast/fastunknot/coefficient_span.py', 'fast/fastunknot/cyclic_overlap_index.py',
    'fast/fastunknot/interval_orbits.py', 'fast/fastunknot/normal_surface_orbits.py',
    'fast/fastunknot/integer_codec.py',
] + ['fast/examples/'+name+'.json' for name in
     ('conway', 'kinoshita_terasaka', 'hard_unknot_8', 'stress_braid5_36',
      'torus_3_5', 'trefoil', 'figure_eight', 'unknot',
      'grid_scrambled_unknot', 'grid_determinant_one_knot')]


def digest_file(path):
    return sha256(path.read_bytes()).hexdigest()


def git_bytes(relative):
    run = subprocess.run(['git', 'show', BASELINE+':'+PREFIX+relative],
                         cwd=PROJECT, capture_output=True)
    return run.stdout if run.returncode == 0 else None


def recorded_check(evidence, source, expected, *, basis='recorded source digest',
                   field=None, recorded_source=None):
    path = PROJECT / source
    actual = digest_file(path) if path.is_file() else None
    result = dict(evidence=evidence, source=source, recorded_sha256=expected,
                  observed_sha256=actual, matches=actual == expected, basis=basis)
    if field is not None:
        result['field'] = field
    if recorded_source is not None:
        result['recorded_source'] = recorded_source
    return result


def raw_inventory(name, data):
    if name == 'coefficient':
        queries = []
        for case in data['knots']:
            queries.append(case['raw_scan'])
            if 'prefix_solves' in case:
                queries.append(case['prefix_solves'])
        for case in data['algebraic']:
            queries.extend((case['solve'], case['compression']))
        return dict(cases=len(data['knots'])+len(data['algebraic']),
                    measured_round_records=sum(len(q['samples']) for q in queries),
                    retains_arm_order=True, retains_elapsed_samples=True,
                    warmup_elapsed_samples_retained=False,
                    note='Warmups are executed and excluded; their raw elapsed times are not stored.')
    if name == 'cyclic_overlap':
        queries = [mode for case in data['rows'] for mode in case['modes'].values()]
        return dict(actual_diagrams=len(data['rows']), kernel_cases=len(data['kernels']),
                    measured_whole_queries=sum(len(s['measurements']) for q in queries
                                               for s in q['samples']),
                    measured_kernel_queries=sum(len(s['measurements']) for q in data['kernels']
                                                for s in q['samples']),
                    retains_arm_order=True, retains_elapsed_samples=True,
                    retains_excluded_warmups=True,
                    complete_certificates=len(data['certificates']))
    if name == 'interval':
        return dict(cases=len(data['rows']),
                    elapsed_samples=sum(len(row['seconds_all']) for row in data['rows']),
                    retains_elapsed_samples=True, randomized_arm_order=False,
                    warmup_exclusion=False,
                    note='Sequential structural scaling experiment; explicit DSU controls have one sample.')
    return dict(normal_cases=len(data['cases']), scaling_cases=len(data['scaling']),
                retains_elapsed_samples=True, randomized_arm_order=True,
                explicit_order_arrays_retained=False,
                order_reconstructible_from_seed_and_script=True,
                excluded_warmup_elapsed_samples_retained=False,
                note='Per-arm lists preserve round indices; the seeded arm order is reconstructible, not explicitly stored.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        default=HERE/'source_hash_audit.json')
    args = parser.parse_args()
    checks, failures, warnings, benchmarks = [], [], [], []
    for name, (script, evidence, field) in BENCHMARKS.items():
        evidence_path = PROJECT/evidence
        if not evidence_path.is_file():
            failures.append(dict(kind='missing evidence', evidence=evidence))
            continue
        data = json.loads(evidence_path.read_text())
        hashes = data.get(field)
        if hashes is None:
            warnings.append(dict(kind='missing measurement source digests', evidence=evidence,
                detail='Current source digests are recorded by this audit only; no historical measurement-source match can be inferred.'))
            for source in (script, 'fast/fastunknot/interval_orbits.py'):
                checks.append(dict(evidence=evidence,source=source,recorded_sha256=None,
                    observed_sha256=digest_file(PROJECT/source),matches=None,
                    basis='post hoc current-source inventory only'))
        else:
            for source, expected in hashes.items():
                checks.append(recorded_check(evidence,'fast/'+source,expected,field=field))
        if name == 'coefficient':
            checks.append(recorded_check(evidence,script,data['benchmark_sha256'],
                                         field='benchmark_sha256'))
        if name == 'interval' and hashes is not None:
            frozen = hashes == data.get('source_sha256_after')
            if not frozen or data.get('measured_sources_unchanged') is not True:
                failures.append(dict(kind='invalid interval freeze evidence',evidence=evidence))
        semantics = {
            'coefficient':'Relevant modules compared before and after timing; benchmark script digest stored at end.',
            'cyclic_overlap':'Listed modules and benchmark script frozen before timing and compared afterward.',
            'interval':'Kernel and benchmark script frozen before timing and compared afterward.' if hashes else
                       'No source freeze fields in this version of the evidence.',
            'normal_surface':'Listed module and script digests stored after timing; no automatic before/after assertion.'
        }[name]
        benchmarks.append(dict(name=name,script=script,evidence=evidence,
            evidence_sha256=digest_file(evidence_path),source_hash_semantics=semantics,
            raw_data=raw_inventory(name,data)))
    baseline_source = git_bytes('fast/fastunknot/relator_overlap.py')
    if baseline_source is None:
        warnings.append(dict(kind='baseline Git object unavailable',
            detail='Cyclic-overlap benchmark needs the pinned commit available to git show. Apply the overlay in that checkout, not in an overlay-only directory.'))
    else:
        evidence = 'fast/cyclic_overlap_research/results.json'
        data = json.loads((PROJECT/evidence).read_text())
        actual = sha256(baseline_source).hexdigest()
        checks.append(dict(evidence=evidence,source=BASELINE+':'+PREFIX+'fast/fastunknot/relator_overlap.py',
            recorded_sha256=data['baseline_overlap_source_sha256'],observed_sha256=actual,
            matches=actual==data['baseline_overlap_source_sha256'],basis='pinned Git object'))
    calibration = PROJECT/'fast/cyclic_overlap_research/calibration_results.json'
    if calibration.is_file():
        data = json.loads(calibration.read_text())
        expected = data['source_sha256']['fastunknot/cyclic_overlap_index.py']
        checks.append(recorded_check('fast/cyclic_overlap_research/calibration_results.json',
            'fast/cyclic_overlap_research/calibration_index.py',expected,
            basis='archived calibration variant', recorded_source='fastunknot/cyclic_overlap_index.py'))
    for check in checks:
        if check['matches'] is False:
            failures.append(dict(kind='source digest mismatch', evidence=check['evidence'],source=check['source']))
    static = []
    personal = re.compile(r'(?:/(?:workspace|tmp|home|Users|mnt|private)/|[A-Za-z]:\\(?:Users|tmp)\\)')
    for relative in [x[0] for x in BENCHMARKS.values()]+TESTS+EXTRA_CHECKED:
        path = PROJECT/relative
        if not path.is_file():
            failures.append(dict(kind='missing script or test',source=relative))
            continue
        text = path.read_text()
        try:
            ast.parse(text,filename=relative)
            parses = True
        except SyntaxError as exc:
            parses = False
            failures.append(dict(kind='syntax error',source=relative,detail=str(exc)))
        hits = [number for number,line in enumerate(text.splitlines(),1) if personal.search(line)]
        if hits:
            failures.append(dict(kind='personal absolute path requires review',source=relative,lines=hits))
        static.append(dict(source=relative,sha256=digest_file(path),ast_parses=parses,
                           personal_absolute_path_hits=hits))
    dependencies = []
    for relative in CRITICAL_DEPENDENCIES:
        path = PROJECT/relative
        original = git_bytes(relative)
        exists = path.is_file()
        current = digest_file(path) if exists else None
        entry = dict(path=relative,exists=exists,current_sha256=current,
            present_at_pinned_commit=original is not None,
            delivery='inherited from pinned checkout' if original is not None else 'required in overlay')
        if original is not None:
            before = sha256(original).hexdigest()
            entry.update(baseline_sha256=before,matches_pinned_bytes=before==current)
            if before != current:
                entry['delivery'] = 'modified file required in overlay'
        if not exists:
            failures.append(dict(kind='missing repository dependency',source=relative))
        dependencies.append(entry)
    logs = []
    for folder in ('fast/coefficient_research','fast/cyclic_overlap_research',
                   'fast/interval_research','fast/normal_orbit_research'):
        for path in sorted((PROJECT/folder).glob('*')):
            if not path.is_file() or path.suffix not in ('.log','.txt'):
                continue
            relative = str(path.relative_to(PROJECT))
            ignored = subprocess.run(['git','check-ignore','--quiet',relative],
                                     cwd=PROJECT).returncode == 0
            logs.append(dict(path=relative,sha256=digest_file(path),gitignored=ignored,
                packaging='explicit inclusion or git add -f required' if ignored else 'ordinary inclusion'))
    warnings.append(dict(kind='normal timing order retention',
        evidence='fast/normal_orbit_research/results.json',
        detail='Raw per-arm timings and seed are retained, but shuffled-order arrays and warmup elapsed samples are not. Describe this accurately rather than claiming every experiment stores explicit order arrays.'))
    warnings.append(dict(kind='overlay application requirement',
        detail='All four benchmarks are portable after applying to the pinned repository. Existing imports/fixtures are intentionally inherited; an overlay-only directory is not a standalone checkout.'))
    report = dict(schema='research_source_hash_audit_v1',baseline_commit=BASELINE,
        paths_relative_to='Topology/UnknotRecognition',
        scope='Static AST/path inspection, recorded digest comparison and pinned Git dependency checks; no benchmarks or tests executed.',
        status='PASS_WITH_NOTES' if not failures else 'FAIL',
        counts=dict(recorded_digest_checks=sum(c['recorded_sha256'] is not None for c in checks),
                    matching_recorded_digests=sum(c['matches'] is True for c in checks),
                    source_mismatches=sum(c['matches'] is False for c in checks),
                    static_python_files=len(static),critical_dependencies=len(dependencies)),
        benchmarks=benchmarks,source_checks=checks,static_python_checks=static,
        repository_dependencies=dependencies,
        test_execution=dict(cwd='Topology/UnknotRecognition/fast',
            command='PYTHONPATH=tests:. python -B -m unittest test_coefficient_span test_cyclic_overlap_index test_interval_orbits test_normal_surface_orbits -v',
            optional_dependency='Regina only for explicitly skipped independent normal-surface oracle tests; no benchmark requires it.',
            plot_regeneration_dependency='Matplotlib only for render_results.py, separate from the four benchmarks.'),
        raw_log_inventory=logs,warnings=warnings,failures=failures)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(status=report['status'],counts=report['counts'],
                          failures=failures,warnings=len(warnings),output=str(args.output))))
    return 1 if failures else 0


if __name__ == '__main__':
    raise SystemExit(main())
