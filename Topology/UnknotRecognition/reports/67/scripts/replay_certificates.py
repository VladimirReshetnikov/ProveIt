#!/usr/bin/env python3
"""Replay all saved mathematical certificates, using only independent verifiers.

Usage, from either the research workspace or the unpacked artifact::

    python scripts/replay_certificates.py
    python scripts/replay_certificates.py --results-dir path/to/results --quiet

Only the Python standard library and the bundled fastunknot code are required;
Regina, LP solvers, candidate producers, and ray enumerators are not called.
The four frozen input JSON files are read without modification.  The default
output is results/reproduced/certificate_replay.json.  Existing files outside
that reproduced directory cannot be overwritten with --output.

Exit 0 means every saved certificate was found and accepted, including both
sector strategies, standalone ray proofs, propagation proofs, and nested disc
proofs.  Exit 1 reports rejected proofs, malformed records, or incomplete replay;
exit 2 reports an input/usage error.  The report identifies failures by JSON
pointer.  INCONCLUSIVE and NOT_CERTIFIED records carry no mathematical proof
and are counted separately.  Boolean-only mutation and ray-check logs cannot
be independently replayed and are explicitly labelled historical observations.
This does not repeat searches, oracle enumerations, timings, or knot recognition.
"""

import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import platform
import sys
from time import perf_counter


ROOT = Path(__file__).resolve().parents[1]
SCHEMAS = {
    'discovery_corpus.json': 'normal-disc-discovery-corpus-v1',
    'sector_euler_audit.json': 'normal-sector-euler-audit-v1',
    'ray_audit.json': 'normal-ray-audit-v1',
    'propagation_audit.json': 'normal-propagation-audit-v1',
}
COMPLETE_STATUSES = {'POSITIVE_EULER', 'NO_POSITIVE_EULER'}
FORBIDDEN_MODULES = {
    'fastunknot.exact_lp', 'fastunknot.normal_euler',
    'fastunknot.normal_sector', 'fastunknot.normal_ray',
    'fastunknot.normal_propagation', 'fastunknot.normal_seed',
    'fastunknot.normal_surface', 'regina',
}


class ReplayInputError(ValueError):
    """A saved record cannot be linked unambiguously to its claimed input."""


def require(condition, explanation):
    if not condition:
        raise ReplayInputError(explanation)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON object key: '+key)
        result[key] = value
    return result


def saved_certificate_paths(document):
    """Inventory every non-null `certificate` field, including unknown places."""
    found = set()
    stack = [('', document)]
    while stack:
        path, value = stack.pop()
        if type(value) is dict:
            for key, child in value.items():
                child_path = path+'/'+key.replace('~', '~0').replace('/', '~1')
                if key == 'certificate' and child is not None:
                    found.add(child_path)
                if type(child) in (dict, list):
                    stack.append((child_path, child))
        elif type(value) is list:
            stack.extend((path+'/'+str(i), child) for i, child in enumerate(value)
                         if type(child) in (dict, list))
    return found


def load_verifiers():
    for candidate in (ROOT/'fast', ROOT/'work'/'fast'):
        if (candidate/'fastunknot'/'normal_euler_verify.py').is_file():
            sys.path.insert(0, str(candidate))
            break
    else:
        raise ReplayInputError('bundled fastunknot verifiers not found in fast/ or work/fast/')
    from fastunknot.normal_euler_verify import verify_sector_euler_certificate
    from fastunknot.normal_ray_verify import verify_normal_ray_disc
    from fastunknot.normal_propagation_verify import verify_normal_propagation_certificate
    return {
        'sector': verify_sector_euler_certificate,
        'ray': verify_normal_ray_disc,
        'propagation': verify_normal_propagation_certificate,
    }, candidate


class Replay:
    def __init__(self, documents, verifiers, quiet=False):
        self.documents = documents
        self.verifiers = verifiers
        self.quiet = quiet
        self.failures = []
        self.counts = defaultdict(Counter)
        self.statuses = defaultdict(Counter)
        self.without_certificate = Counter()
        self.historical = Counter()
        self.attempted = set()
        self.inventory = {
            name+'#'+path
            for name, document in documents.items()
            for path in saved_certificate_paths(document)
        }
        self.fixtures = {}
        self.propagation_cases = {}

    def failure(self, location, reason, kind='data_error'):
        self.failures.append(dict(location=location, kind=kind, reason=reason))
        if not self.quiet:
            print('FAIL '+location+': '+reason, file=sys.stderr, flush=True)

    def record(self, location, operation, *args):
        try:
            operation(location, *args)
        except Exception as exc:
            self.failure(location, type(exc).__name__+': '+str(exc))

    def replay(self, kind, location, verifier, *arguments):
        require(location not in self.attempted, 'duplicate replay of '+location)
        self.attempted.add(location)
        self.counts[kind]['attempted'] += 1
        certificate = arguments[-1]
        status = certificate.get('status', 'DISC_FOUND') if type(certificate) is dict else 'MALFORMED'
        self.statuses[kind][status] += 1
        try:
            accepted = verifier(*arguments)
        except Exception as exc:
            self.counts[kind]['verifier_errors'] += 1
            self.failure(location, type(exc).__name__+': '+str(exc), 'verifier_error')
            return
        if accepted is True:
            self.counts[kind]['accepted'] += 1
        else:
            self.counts[kind]['rejected'] += 1
            self.failure(location, 'independent verifier did not return True', 'rejected_certificate')
        if not self.quiet and len(self.attempted) % 2000 == 0:
            print('Replayed '+str(len(self.attempted))+' saved certificates.', flush=True)

    def euler_answer(self, kind, location, raw, answer, support=None):
        require(type(answer) is dict, 'answer must be an object')
        status = answer.get('status')
        if status == 'INCONCLUSIVE':
            require(answer.get('certificate') is None, 'INCONCLUSIVE answer carries a certificate')
            self.without_certificate[kind+'_inconclusive'] += 1
            return
        require(status in COMPLETE_STATUSES, 'unknown Euler answer status: '+repr(status))
        certificate = answer.get('certificate')
        require(type(certificate) is dict, 'complete Euler answer is missing its certificate')
        require(certificate.get('status') == status, 'answer and certificate statuses differ')
        if support is not None:
            require(certificate.get('allowed_types') == support,
                    'audit support differs from certificate allowed_types')
        if status == 'POSITIVE_EULER' and 'coordinates' in answer:
            require(answer['coordinates'] == certificate.get('coordinates'),
                    'answer and certificate coordinates differ')
        verifier_kind = 'sector' if kind.startswith('sector_') else 'propagation'
        self.replay(kind, location+'/certificate', self.verifiers[verifier_kind], raw, certificate)

    def add_fixture(self, location, fixture):
        require(type(fixture) is dict, 'fixture must be an object')
        name = fixture.get('id')
        require(type(name) is str and name, 'missing fixture id')
        require(name not in self.fixtures, 'duplicate fixture id: '+name)
        require(type(fixture.get('triangulation')) is dict, 'missing fixture triangulation')
        require(type(fixture.get('standard_vertices')) is list, 'missing standard vertex list')
        self.fixtures[name] = fixture

    def sector_record(self, location, record):
        raw = self.fixtures[record['fixture_id']]['triangulation']
        require(type(record.get('support')) is list, 'missing sector support')
        # The anchors audit stores status/certificate directly on its record.
        anchor = dict(status=record.get('new_status'), certificate=record.get('certificate'))
        self.euler_answer('sector_anchors', location, raw, anchor, record['support'])
        self.euler_answer('sector_envelope', location+'/envelope', raw,
                          record['envelope'], record['support'])
        for answer in (record, record['envelope']):
            check = answer.get('ray_check')
            if check is not None:
                require(type(check) is dict and check.get('certificate') is None,
                        'unexpected sector ray proof location; explicit replay support required')
                self.historical['sector_ray_check_records_without_saved_proof'] += 1
                if check.get('status') == 'DISC_FOUND':
                    self.historical['sector_ray_check_disc_found_without_saved_proof'] += 1

    def ray_key(self, record):
        name, index = record['fixture_id'], record['vertex_index']
        require(type(name) is str and name in self.fixtures, 'unknown ray fixture id')
        vertices = self.fixtures[name]['standard_vertices']
        require(type(index) is int and 0 <= index < len(vertices), 'invalid standard vertex index')
        return name, index

    def ray_record(self, location, record, records):
        key = self.ray_key(record)
        require(key not in records, 'duplicate ray comparison fixture/index')
        require(record.get('status') in {'DISC_FOUND', 'NOT_CERTIFIED'}, 'unknown ray answer status')
        records[key] = record
        if record['status'] == 'NOT_CERTIFIED':
            self.without_certificate['standalone_ray_not_certified'] += 1

    def ray_certificate(self, location, record, comparisons, seen):
        key = self.ray_key(record)
        require(key not in seen, 'duplicate saved ray certificate fixture/index')
        seen.add(key)
        require(key in comparisons, 'saved ray certificate lacks its comparison record')
        require(comparisons[key]['status'] == 'DISC_FOUND', 'ray proof linked to non-DISC_FOUND record')
        fixture = self.fixtures[key[0]]
        coordinates = fixture['standard_vertices'][key[1]]['coordinates']
        self.replay('standalone_ray', location+'/certificate', self.verifiers['ray'],
                    fixture['triangulation'], coordinates, record['certificate'])

    def add_propagation_case(self, location, case):
        name = case['name']
        require(type(name) is str and name, 'missing propagation case name')
        require(name not in self.propagation_cases, 'duplicate propagation case name')
        require(type(case.get('triangulation')) is dict, 'missing propagation triangulation')
        self.propagation_cases[name] = case

    def propagation_case(self, location, case):
        raw, answer = case['triangulation'], case['answer']
        self.euler_answer('propagation_case', location+'/answer', raw, answer)
        ray = case.get('normal_ray_disc')
        if ray is None:
            return
        require(answer.get('status') == 'POSITIVE_EULER', 'nested ray answer lacks a positive Euler parent')
        require(type(ray) is dict, 'nested ray answer must be an object')
        if ray.get('status') == 'NOT_CERTIFIED':
            require(ray.get('certificate') is None, 'NOT_CERTIFIED nested ray carries a proof')
            self.without_certificate['propagation_nested_ray_not_certified'] += 1
            return
        require(ray.get('status') == 'DISC_FOUND', 'unknown nested ray status')
        require(ray.get('coordinates') == answer.get('coordinates'),
                'nested ray and parent positive witness coordinates differ')
        self.replay('propagation_nested_disc', location+'/normal_ray_disc/certificate',
                    self.verifiers['ray'], raw, ray['coordinates'], ray['certificate'])

    def redundant_control(self, location, record):
        case = self.propagation_cases[record['source_case']]
        certificate = record['certificate']
        require(certificate.get('status') == 'NO_POSITIVE_EULER',
                'redundant negative control has an unexpected certificate status')
        self.replay('propagation_redundant_control', location+'/certificate',
                    self.verifiers['propagation'], case['triangulation'], certificate)

    def budget_control(self, location, record):
        require(record['source_case'] in self.propagation_cases, 'unknown budget-control source case')
        answer = record['answer']
        require(answer.get('status') == 'INCONCLUSIVE', 'budget control is not INCONCLUSIVE')
        require(answer.get('certificate') is None, 'INCONCLUSIVE budget control carries a proof')
        self.without_certificate['propagation_budget_control_inconclusive'] += 1

    def run(self):
        corpus = self.documents['discovery_corpus.json']
        for i, fixture in enumerate(corpus['records']):
            self.record('discovery_corpus.json#/records/'+str(i), self.add_fixture, fixture)
        sector = self.documents['sector_euler_audit.json']
        require(sector['fixture_count'] == len(self.fixtures), 'sector fixture_count differs from corpus')
        for i, record in enumerate(sector['records']):
            self.record('sector_euler_audit.json#/records/'+str(i), self.sector_record, record)
        rays = self.documents['ray_audit.json']
        require(rays['fixtures'] == len(self.fixtures), 'ray fixture count differs from corpus')
        require(rays['exact_comparisons'] == len(rays['records']), 'ray comparison count mismatch')
        comparisons, seen = {}, set()
        for i, record in enumerate(rays['records']):
            self.record('ray_audit.json#/records/'+str(i), self.ray_record, record, comparisons)
        for i, record in enumerate(rays['certificates']):
            self.record('ray_audit.json#/certificates/'+str(i), self.ray_certificate,
                        record, comparisons, seen)
        missing = {key for key, record in comparisons.items() if record['status'] == 'DISC_FOUND'}-seen
        for name, index in sorted(missing):
            self.failure('ray_audit.json#/certificates', 'missing DISC_FOUND proof for '+name+':'+str(index))
        self.historical['ray_mutation_rejections_without_saved_mutants'] = rays['mutation_rejections']
        propagation = self.documents['propagation_audit.json']
        for i, case in enumerate(propagation['cases']):
            self.record('propagation_audit.json#/cases/'+str(i), self.add_propagation_case, case)
        for i, case in enumerate(propagation['cases']):
            self.record('propagation_audit.json#/cases/'+str(i), self.propagation_case, case)
        for i, record in enumerate(propagation['redundant_replay_controls']):
            self.record('propagation_audit.json#/redundant_replay_controls/'+str(i),
                        self.redundant_control, record)
        for i, record in enumerate(propagation['budget_controls']):
            self.record('propagation_audit.json#/budget_controls/'+str(i), self.budget_control, record)
        self.historical['propagation_mutation_records_without_saved_mutants'] = len(propagation['mutation_controls'])

    def report(self):
        for location in sorted(self.inventory-self.attempted):
            self.failure(location, 'saved certificate was not replayed', 'unreplayed_certificate')
        for location in sorted(self.attempted-self.inventory):
            self.failure(location, 'replayed location is absent from saved certificate inventory', 'inventory_mismatch')
        forbidden = sorted(FORBIDDEN_MODULES & sys.modules.keys())
        if forbidden:
            self.failure('runtime', 'producer/solver/enumerator modules loaded: '+', '.join(forbidden))
        totals = sum(self.counts.values(), Counter())
        return dict(
            status='COMPLETE' if not self.failures else 'FAILED',
            scope='Independent arithmetic replay of saved certificates; no regenerated proofs, searches, oracle enumeration, or recognition.',
            fixture_count=len(self.fixtures),
            propagation_case_count=len(self.propagation_cases),
            saved_certificate_count=len(self.inventory),
            attempted_certificate_count=len(self.attempted),
            accepted_certificate_count=totals['accepted'],
            rejected_certificate_count=totals['rejected'],
            verifier_error_count=totals['verifier_errors'],
            unreplayed_certificate_count=len(self.inventory-self.attempted),
            counts_by_kind={key: dict(value) for key, value in sorted(self.counts.items())},
            status_counts_by_kind={key: dict(value) for key, value in sorted(self.statuses.items())},
            records_without_certificates=dict(sorted(self.without_certificate.items())),
            historical_observations_not_replayed=dict(sorted(self.historical.items())),
            producer_solver_enumerator_modules_loaded=forbidden,
            certificate_inventory_sha256=sha256('\n'.join(sorted(self.inventory)).encode()).hexdigest(),
            failure_count=len(self.failures), failures=self.failures,
        )


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--results-dir', type=Path, default=ROOT/'results')
    parser.add_argument('--output', type=Path, help='default: RESULTS_DIR/reproduced/certificate_replay.json')
    parser.add_argument('--quiet', action='store_true', help='suppress progress; the final summary is still printed')
    args = parser.parse_args()
    results_dir = args.results_dir.resolve()
    reproduced = results_dir/'reproduced'
    output = (args.output or reproduced/'certificate_replay.json').resolve()
    try:
        require(output.suffix == '.json', '--output must have a .json extension')
        require(output not in {(results_dir/name).resolve() for name in SCHEMAS},
                'refusing to overwrite a frozen input file')
        require(not output.is_relative_to(results_dir) or output.is_relative_to(reproduced),
                'outputs inside results must be placed in results/reproduced/')
        require(not output.exists() or output.is_relative_to(reproduced),
                'refusing to overwrite an existing file outside results/reproduced/')
        verifiers, fast_path = load_verifiers()
        documents, inputs = {}, {}
        for name, schema in SCHEMAS.items():
            path = results_dir/name
            encoded = path.read_bytes()
            document = json.loads(encoded, object_pairs_hook=unique_object)
            require(type(document) is dict and document.get('schema') == schema,
                    'unexpected schema in '+name)
            documents[name] = document
            inputs[name] = dict(sha256=sha256(encoded).hexdigest(), bytes=len(encoded))
        require(documents['sector_euler_audit.json']['input_sha256'] == inputs['discovery_corpus.json']['sha256'],
                'sector audit is not bound to the supplied discovery corpus bytes')
    except (OSError, ValueError, KeyError, ImportError) as exc:
        print('Input error: '+str(exc), file=sys.stderr)
        return 2
    replay = Replay(documents, verifiers, args.quiet)
    started = perf_counter()
    interrupted = False
    try:
        replay.run()
    except KeyboardInterrupt:
        interrupted = True
        replay.failure('runtime', 'replay interrupted before completion', 'interrupted')
    except Exception as exc:
        replay.failure('runtime', type(exc).__name__+': '+str(exc), 'data_error')
    report = replay.report()
    report.update(
        schema='normal-saved-certificate-replay-v1',
        date_utc=datetime.now(timezone.utc).isoformat(),
        python=platform.python_version(),
        inputs=inputs,
        verifier_source_sha256={
            name: sha256(Path(sys.modules[function.__module__].__file__).read_bytes()).hexdigest()
            for name, function in sorted(verifiers.items())
        },
        shared_geometry_source_sha256=sha256((fast_path/'fastunknot'/'normal_surface_geometry.py').read_bytes()).hexdigest(),
        shared_parity_source_sha256=sha256((fast_path/'fastunknot'/'normal_surface_parity.py').read_bytes()).hexdigest(),
        replay_script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        elapsed_replay_seconds=perf_counter()-started,
        timing_scope='One replay run; elapsed time is diagnostic, not a controlled performance comparison.',
    )
    try:
        output.parent.mkdir(parents=True, exist_ok=True)
        temporary = output.with_name(output.name+'.tmp')
        temporary.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')
        os.replace(temporary, output)
    except OSError as exc:
        print('Output error: '+str(exc), file=sys.stderr)
        return 2
    print(json.dumps({key: report[key] for key in (
        'status', 'saved_certificate_count', 'attempted_certificate_count',
        'accepted_certificate_count', 'rejected_certificate_count',
        'unreplayed_certificate_count', 'failure_count')}, sort_keys=True))
    print('Report: '+str(output))
    return 130 if interrupted else (0 if report['status'] == 'COMPLETE' else 1)


if __name__ == '__main__':
    raise SystemExit(main())
