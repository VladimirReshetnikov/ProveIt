"""Reproduce finite validation and independently replay saved certificates."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--benchmark', action='store_true')
    ap.add_argument('--output-dir', type=Path)
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    out = (args.output_dir or root/'reproduced').resolve()
    out.mkdir(parents=True, exist_ok=True)
    sys.path.insert(0, str(root))
    from activation_forests import verify_result, verify_output
    from integration.verify_prefix import verify_prefix
    for runner, filename in [('run_checks.py','ordered_tests.json'),
                             ('run_output_checks.py','output_tests.json')]:
        subprocess.run([sys.executable,str(root/runner),'--output',str(out/filename)],
                       cwd=root,check=True)
    native_path = root/'results/native_study.json'
    native = json.loads(native_path.read_text())
    sources = {c['id']:c for c in native['cases']}
    all_problems = {(c['id'],kind):c[kind]['problem'] for c in native['cases']
                    for kind in ('source','finite_boundary')}
    counts = Counter()
    for file, checker in [('native_decisions_ordered.json',verify_result),
                          ('native_decisions_output.json',verify_output)]:
        bank = json.loads((root/'results'/file).read_text())
        assert bank['input_sha256'] == sha256(native_path.read_bytes()).hexdigest()
        for c in bank['cases']:
            for kind in ('source','finite_boundary'):
                r = c[kind]['answer']
                counts[file+'/'+r['status']] += 1
                if r['status'] != 'INCONCLUSIVE':
                    assert checker(sources[c['id']][kind]['problem'],r),(file,c['id'],kind)
    labels = json.loads((root/'results/relabel_study.json').read_text())
    relabels = {'relabel/'+str(c['trial']):c for c in labels['cases']}
    all_problems.update({(key,'finite_boundary'):c['problem'] for key,c in relabels.items()})
    for file, checker in [('relabel_decisions_ordered.json',verify_result),
                          ('relabel_decisions_output.json',verify_output)]:
        bank = json.loads((root/'results'/file).read_text())
        for c in bank['cases']:
            r = c['finite_boundary']['result']
            assert checker(relabels[c['id']]['problem'],r),(file,c['id'])
            counts[file+'/'+r['status']] += 1
    prefixes = json.loads((root/'results/prefix_results.json').read_text())
    for c in prefixes['cases']:
        assert verify_prefix(all_problems[(c['id'],c['matrix'])],c['result'])
        counts['saved_prefix/'+c['result']['status']] += 1
    subprocess.run([sys.executable,str(root/'experiments/evaluate_prefix.py'),
                    '--root',str(root),'--output',str(out/'prefix_results.json')],
                   cwd=root,check=True)
    if args.benchmark:
        subprocess.run([sys.executable,str(root/'experiments/benchmark.py'),
            '--native',str(native_path),'--relabels',str(root/'results/relabel_study.json'),
            '--code',str(root),'--dual-code',str(root/'reference/dual_forest'),
            '--output',str(out/'paired_benchmark.json'),'--repetitions','7',
            '--max-work','1000000','--max-nodes','50000'],cwd=root,check=True)
    manifest = root/'MANIFEST.sha256'
    manifest_verified = 0
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            digest,relative = line.split('  ',1)
            assert sha256((root/relative).read_bytes()).hexdigest() == digest,relative
            manifest_verified += 1
    result = {'success':True,'saved_replay_counts':dict(counts),
        'manifest_files_verified':manifest_verified,
        'scope':'Finite tests and source-bound saved certificates. INCONCLUSIVE records '
                'are counted without accepting them as complete proofs. Native geometry '
                'reconstruction is a separate explicitly documented tier.'}
    (out/'reproduction_summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
