#!/usr/bin/env python3
"""Prepare portable batch171 replay commands; execute no delivered code.

First recover original layouts with recover171.py. This helper reads only its
frozen template and recovered files, then writes a fresh plan directory. It
does not invoke the replay runner or create the selected work directory.
"""
import argparse
import copy
import hashlib
import json
import sys
from pathlib import Path

TEMPLATE_SHA = 'c6a69b78b89d9a1ca35e5abc0580d4357e10ba9a4db68305995e5ca2ef15a98f'

def require(ok, why):
    if not ok:
        raise ValueError(why)

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--recovered', type=Path, required=True)
    ap.add_argument('--runner', type=Path, required=True,
                    help='Maintained root-authored replay171.py, never invoked here.')
    ap.add_argument('--output', type=Path, required=True,
                    help='New external directory for the generated plan/receipt.')
    ap.add_argument('--work', type=Path,
                    help='Absent directory for a later runner invocation; default OUTPUT/work.')
    ap.add_argument('--source', type=int, action='append',
                    help='Choose local source81..100; default all. Sources87/96 also require recovered91 as inert input.')
    args = ap.parse_args()
    require(sys.version_info >= (3, 13), 'This portable compatibility adapter requires Python 3.13 or newer')
    template_path = Path(__file__).resolve().with_name('replay171-template-v2.json')
    require(digest(template_path) == TEMPLATE_SHA, 'Frozen template differs')
    template = json.loads(template_path.read_text())
    recovered = args.recovered.resolve()
    runner = args.runner.resolve()
    output = args.output.resolve()
    work = args.work.resolve() if args.work else output / 'work'
    selected = set(args.source or range(81, 101))
    require(selected and selected <= set(range(81, 101)), 'Invalid selected source')
    require(recovered.is_dir() and runner.is_file(), 'Missing recovery or runner')
    require(not output.exists() and not work.exists(), 'Output/work must be fresh')
    require(not output.is_relative_to(recovered) and not work.is_relative_to(recovered),
            'Do not write into recovered originals')
    require(output != work and not output.is_relative_to(work), 'Work must not contain plan output')
    require(not output.is_relative_to(Path(__file__).resolve().parent),
            'Plan output must be outside the installed helper directory')
    recovery = json.loads((recovered / 'recovery.json').read_text())
    require(recovery['status'] == 'PASS', 'Recovery has not completed')
    available = {x['source'] for x in recovery['packages']}
    required = selected | ({91} if selected & {87, 96} else set())
    require(required <= available, 'Required source layout was not recovered')
    targets = {}
    for n in required:
        wrapper = template['wrappers'][str(n)]
        require(Path(wrapper).name == wrapper and wrapper not in ('.', '..'), 'Unsafe wrapper')
        target = recovered / ('source' + str(n)) / wrapper
        require(target.is_dir() and target.resolve().is_relative_to(recovered), 'Missing/escaping wrapper')
        targets[n] = target.resolve()
    jobs = []
    substitutions = []
    names = set()
    edits_seen = set()
    for original in template['jobs']:
        n = original['source']
        if n not in selected:
            continue
        job = copy.deepcopy(original)
        require(job['name'] not in names and Path(job['name']).name == job['name'], 'Unsafe/duplicate job name')
        names.add(job['name'])
        job['package'] = str(targets[n])
        if job['name'] == 'A16-prepare-local-archive':
            # Our own historical copy job embedded both paths in Python code.
            # Pass them as arguments so quotes/backslashes in a new work path
            # cannot alter the code interpreted by the later runner.
            before_code = job['argv'][3]
            oldzip = template['original_packages']['91'] + '/reference/zfc245-proof-20261018.zip'
            replacements = [('import hashlib,shutil;', 'import hashlib,shutil,sys;'),
                            ('p=Path(' + repr(oldzip) + ')', 'p=Path(sys.argv[1])'),
                            ("d=Path('{COPY}')", 'd=Path(sys.argv[2])')]
            after_code = before_code
            for before, after in replacements:
                require(after_code.count(before) == 1, 'Own copier path adaptation differs')
                after_code = after_code.replace(before, after)
            job['argv'][3] = after_code
            job['argv'].extend([oldzip, '{COPY}'])
            substitutions.append({'job':job['name'], 'argument':3, 'before':before_code,
                                  'after':after_code, 'reason':'Own copy paths moved to argv; hash/copy gates unchanged'})
        # Only A's local archive recovery crosses package boundaries. Handle a
        # Python -c literal with repr, not textual insertion inside quoted code.
        for i, value in enumerate(job['argv']):
            if not isinstance(value, str):
                raise ValueError('Non-string argument')
            changed = value
            for source, old in sorted(template['original_packages'].items(), key=lambda x: -len(x[1])):
                if old not in changed:
                    continue
                sn = int(source)
                require(sn in targets, 'Argument needs an unrecovered source')
                if i and job['argv'][i-1] == '-c':
                    oldzip = old + '/reference/zfc245-proof-20261018.zip'
                    require(sn == 91 and changed.count(repr(oldzip)) == 1,
                            'Unexpected embedded code path')
                    changed = changed.replace(repr(oldzip), repr(str(targets[sn] / 'reference/zfc245-proof-20261018.zip')))
                else:
                    require(changed == old or changed.startswith(old + '/'), 'Unexpected embedded non-code path')
                    changed = str(targets[sn]) + changed[len(old):]
            require(not any(old in changed for old in template['original_packages'].values()),
                    'Historical package path remains')
            if changed != value:
                substitutions.append({'job':job['name'], 'argument':i, 'before':value, 'after':changed})
            job['argv'][i] = changed
        # Validate entry script without importing it. Relative script paths use
        # the same cwd as the root runner. Embedded -c is the pinned own copier.
        argv = job['argv']
        require(argv[:2] == ['python3', '-B'], 'Unexpected interpreter policy')
        if argv[2] != '-c':
            cwd = job.get('cwd', '{COPY}').replace('{COPY}', str(targets[n]))
            script = argv[2].replace('{COPY}', str(targets[n]))
            path = Path(script) if Path(script).is_absolute() else Path(cwd) / script
            require(path.is_file() and path.resolve().is_relative_to(targets[n]), 'Missing/escaping entry script')
        for edit in job.get('edits', []):
            rel = Path(edit['file'])
            require(not rel.is_absolute() and '..' not in rel.parts, 'Unsafe edit path')
            key = (n, str(rel), edit['before'])
            require(key not in edits_seen, 'Repeated edit across jobs')
            edits_seen.add(key)
            p = targets[n] / rel
            require(p.resolve().is_relative_to(targets[n]) and p.read_text().count(edit['before']) == 1,
                    'Pinned wrapper adaptation no longer matches')
        jobs.append(job)
    require(jobs, 'No jobs selected')
    plan = {'status':'PREPARED_NOT_EXECUTED', 'jobs':jobs,
            'scope':template['scope'], 'template_sha256':TEMPLATE_SHA}
    # Complete every validation before creating any output.
    output.mkdir(parents=True, exist_ok=False)
    plan_path = output / 'jobs.json'
    plan_path.write_text(json.dumps(plan, indent=2) + '\n')
    command = ['python3', '-B', str(runner), str(plan_path), '--output', str(work)]
    receipt = {'status':'PREPARED_NOT_EXECUTED', 'selected_sources':sorted(selected),
               'required_recovered_sources':sorted(required), 'jobs':len(jobs),
               'template':{'path':str(template_path), 'sha256':TEMPLATE_SHA},
               'runner':{'path':str(runner), 'sha256':digest(runner)},
               'recovery':{'path':str(recovered/'recovery.json'), 'sha256':digest(recovered/'recovery.json')},
               'plan':{'path':str(plan_path), 'sha256':digest(plan_path)},
               'path_substitutions':substitutions, 'future_work':str(work),
               'command':command, 'executed_delivered_code':False,
               'warning':'The later runner records exit statuses. Review substantive result JSON/log gates separately; selected leaves are not the complete delivered suites.'}
    (output / 'preparation.json').write_text(json.dumps(receipt, indent=2) + '\n')
    (output / 'command.json').write_text(json.dumps(command, indent=2) + '\n')
    print(json.dumps({'status':receipt['status'], 'jobs':len(jobs), 'command':command}, indent=2))

if __name__ == '__main__':
    main()
