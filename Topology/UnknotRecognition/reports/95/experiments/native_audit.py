"""Fresh source-bound audit against both the pinned consumer and actual cuts."""

import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess
import sys
import time

from fastunknot.integer_codec import encoded_integer, json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from normal_cut_saturation import normal_cut_saturation
from normal_cut_saturation_verify import verify_normal_cut_saturation


ROOT = Path(__file__).resolve().parents[1]


def oracle(case):
    """Build the literal cut in Regina, without any relative bundle model."""
    import regina
    from normal_orbit_research.fixtures import regina_triangulation, regina_surface
    rows = [[encoded_integer(x) for x in row] for row in case['coordinates']]
    weight = sum(map(sum, rows))
    if weight > 4096:
        return dict(status='NOT_ATTEMPTED_EXPANSION_CAP', normal_discs=weight,
                    cap=4096)
    triangulation = regina_triangulation(case['triangulation'])
    surface = regina_surface(triangulation, rows)
    cut = surface.cutAlong()
    values = [part.recogniseHandlebody() for part in cut.triangulateComponents()]
    counts = Counter(values)
    return dict(status='COMPLETE', regina_version=regina.versionString(),
                tetrahedra=cut.size(), components=len(values),
                histogram=[dict(genus=g, multiplicity=n) for g, n in sorted(counts.items())])


def audit(output, timeout):
    bank = json.loads((ROOT / 'data/native_corpus.json').read_text())
    counts, records = Counter(), []
    proof_dir = ROOT / 'data/certificates'
    proof_dir.mkdir(exist_ok=True)
    started = time.perf_counter()
    saved_control = saved_large = saved_obstruction = False
    for i, case in enumerate(bank['cases']):
        raw, rows = case['triangulation'], case['coordinates']
        old = normal_cut_handlebodies(raw, rows)
        new = normal_cut_saturation(raw, rows, record_certificate=True)
        record = dict(id=case['id'], baseline_status=old['status'],
                      baseline_reason=old.get('reason'), status=new['status'],
                      reason=new.get('reason'), stats=new['stats'])
        counts['baseline_' + old['status']] += 1
        counts[new['status']] += 1
        if 'certificate' in new:
            assert verify_normal_cut_saturation(raw, rows, new['certificate']), case['id']
            counts['independent_replays'] += 1
            if new['status'] == 'INCONCLUSIVE':
                counts['raw_obstruction_replays'] += 1
        if new['status'] == 'COMPLETE':
            record['census'] = new['census']
            if old['status'] == 'COMPLETE':
                assert old['census']['histogram'] == new['census']['histogram'], case['id']
                counts['preserved_baseline_successes'] += 1
            else:
                counts['new_successes'] += 1
        elif old['status'] == 'COMPLETE':
            raise AssertionError(('lost baseline success', case['id'], new))
        else:
            counts['inconclusive_' + new['reason']] += 1
        try:
            process = subprocess.run([sys.executable, str(Path(__file__).resolve()), '--oracle'],
                                     input=json.dumps(case), text=True, capture_output=True,
                                     timeout=timeout)
            if process.returncode:
                raise RuntimeError(process.stderr)
            reference = json.loads(process.stdout)
        except subprocess.TimeoutExpired:
            reference = dict(status='TIMEOUT', seconds=timeout)
        record['regina'] = reference
        counts['regina_' + reference['status']] += 1
        large = reference['status'] == 'NOT_ATTEMPTED_EXPANSION_CAP'
        if reference['status'] == 'COMPLETE' and new['status'] == 'COMPLETE':
            assert reference['histogram'] == new['census']['histogram'], record
            counts['certified_regina_agreements'] += 1
        save = (new['status'] == 'COMPLETE' and old['status'] != 'COMPLETE')
        category = 'new'
        if not save and new['status'] == 'COMPLETE' and large and not saved_large:
            save, saved_large, category = True, True, 'binary'
        if not save and new['status'] == 'COMPLETE' and not large and not saved_control:
            save, saved_control, category = True, True, 'legacy'
        if (not save and new['status'] == 'INCONCLUSIVE' and 'certificate' in new
                and not saved_obstruction):
            save, saved_obstruction, category = True, True, 'obstruction'
        if save:
            name = f'{i:03d}_{category}.json'
            payload = dict(id=case['id'], triangulation=raw, coordinates=rows,
                           certificate=new['certificate'])
            (proof_dir / name).write_text(json.dumps(json_safe(payload), indent=2) + '\n')
            record['saved_certificate'] = name
        records.append(record)
        if (i + 1) % 10 == 0:
            print(json.dumps(dict(done=i + 1, counts=counts)), flush=True)
    report = dict(inspected_revision='704600626606a9097cfd89d4e3d2bbc63c8dd1cb',
                  corpus_revision=bank['source_revision'], python=sys.version,
                  counts=counts, cases=records,
                  elapsed_seconds=time.perf_counter() - started,
                  timing_scope='Audit duration only; not a controlled performance comparison.')
    output.write_text(json.dumps(json_safe(report), indent=2) + '\n')
    print(json.dumps(dict(counts=counts, elapsed_seconds=report['elapsed_seconds'])), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--oracle', action='store_true')
    parser.add_argument('--output', type=Path, default=ROOT / 'data/native_audit.json')
    parser.add_argument('--timeout', type=float, default=15)
    args = parser.parse_args()
    if args.oracle:
        print(json.dumps(json_safe(oracle(json.load(sys.stdin)))))
    else:
        audit(args.output, args.timeout)
