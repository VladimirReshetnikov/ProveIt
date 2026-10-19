#!/usr/bin/env python3
"""Replay the portable state experiments using Python 3 and a C++17 compiler.

This reproduces finite discovery screens and a scoped structural census.
It does not certify any machine with fewer than 246 working states.
"""
from pathlib import Path
import sys
sys.dont_write_bytecode=True
from state_paths import output_directory
import argparse,json,re,subprocess,tempfile,time,os

ROOT=Path(__file__).resolve().parents[2]
OUT=None

def run(command,stdout,stderr=None):
    begun=time.monotonic()
    environment=dict(os.environ,ZFC_STATE_OUTPUT=str(OUT),PYTHONDONTWRITEBYTECODE='1')
    (OUT/stdout).parent.mkdir(parents=True,exist_ok=True)
    with (OUT/stdout).open('w') as stream:
        if stderr:
            with (OUT/stderr).open('w') as errors:
                subprocess.run(command,cwd=ROOT,stdout=stream,stderr=errors,env=environment,check=True)
        else:
            subprocess.run(command,cwd=ROOT,stdout=stream,env=environment,check=True)
    elapsed=time.monotonic()-begun
    print(f'PASS {stdout}: {elapsed:.2f} seconds',flush=True)
    return elapsed

def main():
    global OUT
    ap=argparse.ArgumentParser()
    ap.add_argument('--cxx',default='c++')
    ap.add_argument('--python',default='python3')
    ap.add_argument('--output',type=Path,help='Fresh verification directory; packaged input/certificate directories are forbidden')
    args=ap.parse_args();assert __debug__
    OUT=output_directory(args.output)
    print(f'State verification outputs: {OUT}',flush=True)
    elapsed={}
    for script in ('check_selector_commutation','coverage','permutation_rebracket','global_transfer_regions'):
        elapsed[script]=run([args.python,f'code/state/{script}.py'],f'{script}_replay.log')
    for stem in ('s3_best_010','s7_best_018','s9_best_007'):
        cmd=[args.python,'code/state/prepare_colored_quotient.py',f'experiments/state/inputs/{stem}']
        if stem!='s3_best_010':cmd.append('--derive-quotient')
        elapsed[stem+'_prepare']=run(cmd,f'{stem}/preparation_replay.log')
    with tempfile.TemporaryDirectory(prefix='zfc-state-replay-') as tmp:
        binaries={}
        for source in ('quotient_incoming_search','quotient_incoming_gap64','quotient_scanner_compensation','permutation_bisim','blank_start_survey'):
            binary=str(Path(tmp)/source)
            subprocess.run([args.cxx,'-O3','-std=c++17',f'code/state/{source}.cpp','-o',binary],cwd=ROOT,check=True)
            binaries[source]=binary
        elapsed['baseline_incoming']=run([
            binaries['quotient_incoming_search'],
            'vendor/context246/machine/zfc_prefix246_old.tm',
            'experiments/state/baseline/decoder.txt',
            'experiments/audit_inputs/quotient_cases.txt','incoming'],
            'quotient_incoming_results.txt','quotient_incoming_progress.txt')
        elapsed['s3_incoming']=run([
            binaries['quotient_incoming_gap64'],
            'experiments/state/inputs/s3_best_010.tm',
            str(OUT/'s3_best_010/decoder.txt'),
            str(OUT/'s3_best_010/quotient_cases.txt'),'incoming'],
            's3_best_010/incoming_results.txt','s3_best_010/incoming_progress.txt')
        for stem in ('s3_best_010','s7_best_018','s9_best_007'):
            elapsed[stem+'_scanner']=run([
                binaries['quotient_scanner_compensation'],
                f'experiments/state/inputs/{stem}.tm',
                str(OUT/stem/'decoder.txt'),
                str(OUT/stem/'quotient_cases.txt'),'scanner'],
                f'{stem}/scanner_compensation_results.txt',
                f'{stem}/scanner_compensation_progress.txt')
            progress=(OUT/stem/'scanner_compensation_progress.txt').read_text()
            failed=[int(i) for i in re.findall(r'^FAILED_CASE (\d+)$',progress,re.M)]
            case_map=json.loads((OUT/stem/'case_map.json').read_text())
            (OUT/stem/'scanner_failed_cases.json').write_text(
                json.dumps([case_map[i] for i in sorted(failed)],indent=2)+'\n')
        elapsed['rotated_permutation_census']=run([
            binaries['permutation_bisim'],
            'experiments/state/inputs/zfc_rotated246_old.tm'],
            'rotated_permutation_census.txt','rotated_permutation_census_summary.txt')
        elapsed['s10_blank_start_survey']=run([
            binaries['blank_start_survey'],
            'experiments/state/inputs/s10_best_004.tm','2000000'],
            's10_blank_start_survey.jsonl','s10_blank_start_summary.txt')
    (OUT/'replay_timing.json').write_text(json.dumps(elapsed,indent=2)+'\n')
    print('All state campaigns replayed. No sub-246 success is asserted.')

if __name__=='__main__':main()
