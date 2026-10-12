"""Compare canonical and deferred forests on authenticated native cut inputs."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--fast-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--certificates', type=Path, required=True)
    parser.add_argument('--oracle-timeout', type=float, default=20)
    parser.add_argument('--limit', type=int)
    args = parser.parse_args()
    fast = args.fast_root.resolve()
    sys.path.insert(0, str(fast))
    from fastunknot.integer_codec import json_safe
    from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
    from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.certificates.mkdir(parents=True, exist_ok=True)
    files = ['core_handlebody.py', 'bundle_boundary_kernel.py',
             'bundle_boundary_kernel_verify.py', 'normal_cut_handlebodies.py']
    pins = {n: hashlib.sha256((fast/'fastunknot'/n).read_bytes()).hexdigest()
            for n in files}
    bank = []
    for name, group in [('corpus.json', 'historical'),
                        ('three_handle_corpus.json', 'interior_extension')]:
        cases = json.loads((fast/'marked_parallelity_research'/name).read_text())['cases']
        bank.extend((group, c) for c in cases)
    if args.limit is not None:
        bank = bank[:args.limit]
    counts, records = Counter(), []
    start = time.perf_counter()
    for index, (group, case) in enumerate(bank):
        record = dict(id=case['id'], group=group)
        results = {}
        for strategy in ('canonical', 'deferred'):
            begin = time.perf_counter()
            result = normal_cut_handlebodies(case['triangulation'], case['coordinates'],
                record_certificate=True, forest_strategy=strategy)
            produced = time.perf_counter()
            item = dict(status=result['status'], reason=result.get('reason'),
                        produce_seconds=produced-begin)
            counts[group+'/'+strategy+'/'+result['status']] += 1
            if result['status'] == 'COMPLETE':
                assert verify_normal_cut_handlebodies(case['triangulation'],
                    case['coordinates'], result['certificate']), (case['id'], strategy)
                encoded = json.dumps(json_safe(result['certificate']), sort_keys=True).encode()
                item.update(replay_seconds=time.perf_counter()-produced,
                    histogram=result['census']['histogram'], certificate_bytes=len(encoded),
                    certificate_sha256=hashlib.sha256(encoded).hexdigest(),
                    schema=result['certificate']['schema'],
                    kernel_schema=result['certificate'].get('kernel', {}).get('schema'))
                counts['independent_replays'] += 1
            record[strategy] = item
            results[strategy] = result
        if record['canonical']['status'] == 'COMPLETE':
            assert record['deferred']['status'] == 'COMPLETE', record
            assert record['canonical']['histogram'] == record['deferred']['histogram'], record
        else:
            if record['deferred']['status'] == 'COMPLETE':
                counts['new_whole_cut_certificates'] += 1
                packet = dict(source=case, certificate=results['deferred']['certificate'])
                name = case['id'].replace('/', '__')+'.json'
                (args.certificates/name).write_text(json.dumps(json_safe(packet), indent=2)+'\n')
                record['packet'] = name
        try:
            completed = subprocess.run([sys.executable, '-m',
                'marked_parallelity_research.audit_census', '--oracle'],
                input=json.dumps(case), text=True, capture_output=True,
                timeout=args.oracle_timeout, cwd=fast)
            if completed.returncode:
                raise RuntimeError(completed.stderr)
            reference = json.loads(completed.stdout)
            record['regina'] = reference
            if 'histogram' in reference:
                counts['regina_completed'] += 1
                if record['deferred']['status'] == 'COMPLETE':
                    assert reference['histogram'] == record['deferred']['histogram'], record
                    counts['deferred_regina_agreements'] += 1
            else:
                counts['regina_expansion_cap'] += 1
        except subprocess.TimeoutExpired:
            record['regina'] = dict(status='TIMEOUT', seconds=args.oracle_timeout)
            counts['regina_timeout'] += 1
        records.append(record)
        report = dict(finished=False, source_revision='c6d0ec8aa0b6308310ab6c081ba29d8bc363ede5',
            source_sha256=pins, counts=counts, seconds=time.perf_counter()-start, cases=records)
        args.output.write_text(json.dumps(json_safe(report), indent=2)+'\n')
        if (index+1) % 10 == 0 or record.get('packet'):
            print(json.dumps(dict(done=index+1, id=case['id'], counts=counts)), flush=True)
    assert pins == {n: hashlib.sha256((fast/'fastunknot'/n).read_bytes()).hexdigest()
                    for n in files}, 'production source changed during audit'
    report['finished'] = True
    args.output.write_text(json.dumps(json_safe(report), indent=2)+'\n')
    print(json.dumps(dict(finished=True, counts=counts)), flush=True)


if __name__ == '__main__':
    main()
