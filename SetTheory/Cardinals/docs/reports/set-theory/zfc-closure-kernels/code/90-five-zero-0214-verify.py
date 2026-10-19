#!/usr/bin/env python3
"""Reproduce frozen codec, matrix, and CP controls into a separate output path."""
from __future__ import annotations
import argparse, hashlib, json, subprocess, sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    if not __debug__:raise RuntimeError('Run without Python optimization; assertions are required.')
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();out=a.output.resolve()
    protected=[HERE/'codec-source-results',HERE/'cp-fusion-results',HERE/'inputs',HERE/'backend',HERE/'notices']
    assert out!=HERE and not any(out==r or r in out.parents for r in protected),'Output would overwrite frozen artifacts.'
    frozen=[f for root in protected for f in root.rglob('*') if f.is_file() and '__pycache__' not in f.parts]
    before={str(f.relative_to(HERE)):sha(f) for f in frozen}
    out.mkdir(parents=True,exist_ok=True)
    commands=[
        ['codec_source_experiment.py','--output-dir',str(out/'codec-source-results')],
        ['check_codec_experiments.py','--backend',str(HERE/'backend'),'--output-dir',str(out/'codec-source-results')],
        ['check_truth_restriction.py','--output',str(out/'codec-source-results/truth-restriction-matrix.json')],
        ['cp_fusion_experiment.py','--backend',str(HERE/'backend'),'--output-dir',str(out/'cp-fusion-results')],
    ]
    for args in commands:
        completed=subprocess.run([sys.executable,'-B',str(HERE/args[0]),*args[1:]],cwd=HERE,capture_output=True,text=True)
        (out/(args[0]+'.stdout.txt')).write_text(completed.stdout)
        (out/(args[0]+'.stderr.txt')).write_text(completed.stderr)
        assert completed.returncode==0,(args[0],completed.stderr)
        print(args[0]+': PASS',flush=True)
    comparisons=[]
    for folder in ('codec-source-results','cp-fusion-results'):
        for original in sorted((HERE/folder).glob('*')):
            if not original.is_file() or original.suffix not in ('.json','.tm'):continue
            reproduced=out/folder/original.name
            assert reproduced.exists(),reproduced
            if original.suffix=='.json':assert json.loads(original.read_text())==json.loads(reproduced.read_text()),str(original)
            else:assert original.read_bytes()==reproduced.read_bytes(),str(original)
            comparisons.append(str(original.relative_to(HERE)))
    assert all(sha(HERE/f)==h for f,h in before.items()),'A frozen input or result changed.'
    r={'status':'PASS','frozen_artifacts_unchanged':len(before),'exact_reproductions':len(comparisons),'files':comparisons,
       'scope':'Finite codec/register/matrix/CP and raw compiler controls only; no new consistency-machine proof.'}
    (out/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:v for k,v in r.items() if k!='files'},indent=2))
if __name__=='__main__':main()
