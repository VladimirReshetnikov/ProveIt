#!/usr/bin/env python3
"""Run the delivered positive certificates without changing delivered results.

This checks finite computations. The unbounded proof uses the mathematical
arguments and explicitly attributed generic/Box lemmas in the report.
"""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, tempfile

ROOT=Path(__file__).resolve().parent


def check_manifest():
    path=ROOT/'SHA256SUMS'
    if not path.exists():return None
    count=0
    for line in path.read_text().splitlines():
        digest,name=line.split('  ',1)
        file=ROOT/name
        if not file.is_file() or hashlib.sha256(file.read_bytes()).hexdigest()!=digest:
            raise ValueError('SHA-256 mismatch: '+name)
        count+=1
    return count


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    if not __debug__:raise ValueError('Assertions must be enabled; do not use -O')
    manifest=check_manifest()
    source=(ROOT/'upstream/Dag254.v').read_bytes()
    old=b'| 130 => (ENode 123, ENode 166)'
    new=b'| 130 => (ENode 123, ENode 197)'
    if source.count(old)!=1 or (ROOT/'source/Dag254_cache_mp.v').read_bytes()!=source.replace(old,new):
        raise ValueError('The delivered edited source is not the exact one-edge change')
    results={}
    with tempfile.TemporaryDirectory(prefix='cachemp252-check-') as tmp:
        td=Path(tmp)
        stages=[
          ('bootstrap',[ROOT/'machine/verify_bootstrap.py','--directory',ROOT/'machine']),
          ('source_commands',[ROOT/'checks/verify_source.py','--dag',ROOT/'upstream/Dag254.v']),
          ('source_binding',[ROOT/'source-binding/verify_source_binding.py','--directory',ROOT/'source-binding']),
          ('affine',[ROOT/'checks/verify_affine.py'])]
        for label,command in stages:
            output=td/(label+'.json')
            proc=subprocess.run([sys.executable,'-B',*map(str,command),'--output',str(output)],
                                capture_output=True,text=True)
            if proc.returncode:
                print(proc.stdout,file=sys.stderr);print(proc.stderr,file=sys.stderr)
                raise RuntimeError(label+' verification failed')
            results[label]=json.loads(output.read_text())
            print(label+': PASS',flush=True)
    b=results['bootstrap'];s=results['source_binding'];a=results['affine']
    report={'status':'PASS','working_states':b['working_states'],'transition_rows':b['transitions'],
            'blank_steps':b['blank_steps_each_replay'],'independent_blank_replays':b['independent_literal_replays'],
            'canonical_sha256':b['canonical_sha256'],'preserved_box_rows':b['box_support_rows_unchanged'],
            'source_binding':s['new_segment_bisimulation'],
            'source_command_checks':results['source_commands'],
            'affine_cases':a['cases_checked'],'minimum_literal_progress':a['minimum_literal_progress'],
            'manifest_files_checked':manifest,
            'scope':'Finite exact source and machine certificates pass; ordinary unbounded proofs are in the report. No new proof-assistant build or sub-252 machine is claimed.'}
    if args.output:args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
