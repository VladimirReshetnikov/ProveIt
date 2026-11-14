#!/usr/bin/env python3
"""Fast independent checks, with optional slower C++ discovery/search reruns."""
import argparse, gzip, hashlib, json, shutil, subprocess, sys, tempfile
from pathlib import Path
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'code'))
from check_window import check as check_window, need
from sixzero_counterexample import check as check_sixzero

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, help='Optional fresh JSON receipts directory')
    p.add_argument('--discover-window', action='store_true', help='Compile and recompute the abstract fixed point')
    p.add_argument('--search-folds', action='store_true', help='Compile and repeat the full finite primitive fold search')
    p.add_argument('--search-reachable-folds', action='store_true', help='Repeat the source-invariant-filtered sampled primitive fold search')
    args = p.parse_args()
    window = check_window(ROOT)
    counterexample = check_sixzero(ROOT)
    brief = dict(counterexample)
    brief.pop('old_second_trace')
    brief.pop('new_second_trace')
    print(json.dumps({'window_invariant': window, 'rejected_shortcut': brief}, indent=2))
    if args.output:
        args.output.mkdir(parents=True, exist_ok=True)
        (args.output / 'window.json').write_text(json.dumps(window, indent=2) + '\n')
        (args.output / 'rejected_sixzero.json').write_text(json.dumps(counterexample, indent=2) + '\n')
    if args.discover_window or args.search_folds or args.search_reachable_folds:
        compiler = shutil.which('g++') or shutil.which('c++')
        need(compiler, 'Optional searches require a C++17 compiler')
        with tempfile.TemporaryDirectory(prefix='context-research-') as folder:
            work = Path(folder)
            if args.discover_window:
                exe = work / 'window_reach'
                subprocess.run([compiler, '-O3', '-std=c++17', str(ROOT / 'code/window_reach.cpp'), '-o', str(exe)], check=True)
                output = work / 'window.bin'
                subprocess.run([str(exe), str(ROOT / 'data/u208.native.tm'), '7', str(output), 'all'], check=True)
                expected = gzip.decompress((ROOT / 'evidence/window7.bin.gz').read_bytes())
                need(output.read_bytes() == expected, 'Fresh fixed point differs from saved invariant')
                print('Fresh fixed-point reconstruction: PASS')
            if args.search_folds:
                exe = work / 'global_folds'
                subprocess.run([compiler, '-O3', '-std=c++17', str(ROOT / 'code/global_fold_scan.cpp'), '-o', str(exe)], check=True)
                result = subprocess.run([str(exe), str(ROOT / 'data/u208.native.tm'), str(ROOT / 'data/sites.tsv')], check=True, capture_output=True, text=True)
                print(result.stderr.strip())
                need(not result.stdout.strip(), 'Search returned a new finite survivor; inspect it')
                print('Global finite fold search: reproduced no survivors')
                if args.output:
                    (args.output / 'global_folds.log').write_text(result.stderr)
            if args.search_reachable_folds:
                trits = json.loads((ROOT / 'data/register6_trit_invariant.json').read_text())
                trit_text = ''.join(str(sum(1 << value for value in values)) + '\n' for values in trits)
                need(trit_text == (ROOT / 'data/r6_trits.tsv').read_text(), 'Register6 trit conversion changed')
                exe = work / 'reachable_folds'
                subprocess.run([compiler, '-O3', '-std=c++17', str(ROOT / 'code/global_fold_sampled_masks.cpp'), '-o', str(exe)], check=True)
                result = subprocess.run([str(exe), str(ROOT / 'data/u208.native.tm'), str(ROOT / 'data/sites.tsv'), str(ROOT / 'data/zero_positive_invariant.bin'), str(ROOT / 'data/r6_trits.tsv')], check=True, capture_output=True, text=True)
                print(result.stderr.strip())
                need(not result.stdout.strip(), 'Reachable-mask search returned a finite survivor; inspect it')
                print('Reachable-mask sampled fold search: reproduced no survivors')
                if args.output:
                    (args.output / 'reachable_folds.log').write_text(result.stderr)
    print('All requested checks passed. No accepted 207-state construction is claimed by this capsule.')
if __name__ == '__main__':
    main()
