#!/usr/bin/env python3
"""Replay the PA194NQ release in an isolated temporary copy, without network.

Python 3.10+, standard library only. Assertions must be enabled.
The executable checks support the ordinary proof in report/pa194nq.pdf;
they do not claim a newly exported proof-assistant consistency theorem.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
EXPECTED = 'd1cf0f6e7a3c8f999d045694efc107dd1f9a03d45dd6c15e3d197ff7754c7231'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest():
    manifest = ROOT / 'SHA256SUMS'
    need(manifest.is_file(), 'Missing release manifest SHA256SUMS.')
    count = 0
    for line in manifest.read_text().splitlines():
        expected, relative = line.split('  ', 1)
        path = ROOT / relative
        need(path.resolve().is_relative_to(ROOT), 'Manifest path escapes the release.')
        need(path.is_file(), 'Missing release file: ' + relative)
        need(digest(path) == expected, 'Release hash mismatch: ' + relative)
        count += 1
    need(count > 100, 'Unexpectedly short release manifest.')
    print('PASS release hashes:', count, 'files', flush=True)
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true',
                        help='Omit the independent universal tape replay; not a full verification.')
    parser.add_argument('--with-rejected-physical', action='store_true',
                        help='Also rebuild and physically check the rejected 193-state experiment.')
    parser.add_argument('--search', action='store_true',
                        help='Also repeat the packaged pair-quotient searches (longer).')
    parser.add_argument('--keep-work', action='store_true',
                        help='Keep the temporary copy and per-check logs after completion.')
    args = parser.parse_args()
    need(sys.version_info >= (3, 10), 'Python 3.10 or later is required.')
    need(__debug__ and not os.environ.get('PYTHONOPTIMIZE'),
         'Run with assertions enabled; remove -O and PYTHONOPTIMIZE.')
    started = time.monotonic()
    checked_files = check_manifest()
    parent = Path(tempfile.mkdtemp(prefix='pa194nq-replay-'))
    work = parent / 'release'
    shutil.copytree(ROOT, work, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
    logs = parent / 'logs'
    logs.mkdir()
    outcomes = []
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    environment.pop('PYTHONOPTIMIZE', None)

    def run(name, *arguments):
        before = time.monotonic()
        log = logs / (name + '.log')
        with log.open('w') as stream:
            result = subprocess.run([sys.executable, '-B', *arguments], cwd=work,
                                    env=environment, stdout=stream,
                                    stderr=subprocess.STDOUT, check=False)
        if result.returncode:
            print(log.read_text(), file=sys.stderr)
            raise RuntimeError(name + ' failed; logs: ' + str(log))
        seconds = round(time.monotonic() - before, 3)
        outcomes.append({'check': name, 'status': 'PASS', 'seconds': seconds})
        print('PASS', name, '(' + str(seconds) + ' s)', flush=True)

    try:
        run('construction', 'construction/build.py')
        for relative in ('machine.tm', 'machine.native.tm', 'raw.native.tm',
                         'instructions.json', 'sites.json', 'labels.json',
                         'nodes.json', 'local_folds.json', 'macro_word.json'):
            need((ROOT / 'machine' / relative).read_bytes() ==
                 (work / 'machine' / relative).read_bytes(),
                 'Reconstructed artifact differs: machine/' + relative)
        need(digest(work / 'machine/machine.tm') == EXPECTED, 'Wrong accepted table.')
        print('PASS exact reconstructed machine and source artifacts', flush=True)
        if not args.quick:
            run('independent_physical', 'verification/check.py')
            receipt = json.loads((work / 'evidence/independent/receipt.json').read_text())
            need(receipt['universal_source_outcomes'] == 4755 and
                 receipt['complete_blank_tape_equal'] and receipt['startup_steps'] == 58154,
                 'Independent physical receipt mismatch.')
        else:
            print('OMITTED independent universal tape replay (--quick)', flush=True)
        run('commands', 'mathematics/check_commands.py')
        run('exchange_binding', 'mathematics/check_exchange_binding.py')
        run('exchange_certificate', 'mathematics/exchange_certificate.py')
        run('independent_emitter', 'comparison/check_nq_emitter.py',
            '--grammar', 'construction/inputs/q.grammar.json',
            '--instructions', 'machine/instructions.json',
            '--baseline-n-instructions', 'construction/inputs/n.instructions.json',
            '--machine', 'machine/machine.tm',
            '--exchange', 'mathematics/exchange_certificate.json',
            '--output', 'comparison/nq_emitter_review.json')
        run('novelty', 'comparison/check_novelty.py', 'machine/machine.tm',
            '--output', 'evidence/novelty.json')
        novelty = json.loads((work / 'evidence/novelty.json').read_text())
        need(novelty['prior_194_classes'] == 34 and novelty['structurally_absent'],
             'Novelty comparison mismatch.')
        run('factor3_numeric', 'search/factor3_obstruction/check.py')
        run('factor3_primitive', 'search/factor3_obstruction/verify_primitive.py')
        obstruction = json.loads((work / 'search/factor3_obstruction/primitive_result.json').read_text())
        need(obstruction['primitive_proof_steps'] == 73393 and
             obstruction['final_conclusion'] == 1, 'Factor-three certificate mismatch.')
        if args.with_rejected_physical:
            run('rejected193_construction', 'search/build_rejected193.py')
            run('rejected193_independent', 'verification/check.py',
                '--machine', 'search/rejected193',
                '--output', 'search/rejected193/independent')
            need(digest(work / 'search/rejected193/machine.tm') ==
                 'dedb74819ee59e096a6a6c36448e13a1dc8df9363085b183ff5d0838bbbf215a',
                 'Rejected experiment changed.')
        if args.search:
            run('nq_pair_search', 'search/search_nq_pairs.py')
            run('protected_pair_search', 'search/protected_runtime/search.py', 'pp')
            run('mixed_pair_search', 'search/protected_runtime/search.py', 'mixed')
            pairs = json.loads((work / 'search/nq_pairs_result.json').read_text())
            need(pairs['candidates'] == 58140 and not pairs['survivors'],
                 'NQ pair-search receipt mismatch.')
        result = {
            'status': 'PASS (quick; independent physical replay omitted)' if args.quick else 'PASS',
            'accepted_machine': 'PA194NQ', 'working_states': 194,
            'dense_sha256': EXPECTED, 'release_files_checked': checked_files,
            'checks': outcomes, 'seconds': round(time.monotonic() - started, 3),
            'proof_scope': 'Ordinary PA-formalizable argument and executable certificates; no new Lean/Rocq/iPRA endpoint.',
            'sub194_result': 'No accepted smaller machine; the physically valid 193-state factor-three calculus is inconsistent.'
        }
        print(json.dumps(result, indent=2), flush=True)
    except Exception:
        print('Replay failed; temporary artifacts retained at ' + str(parent), file=sys.stderr)
        raise
    else:
        if args.keep_work:
            print('Temporary artifacts retained at ' + str(parent), flush=True)
        else:
            shutil.rmtree(parent)


if __name__ == '__main__':
    main()

