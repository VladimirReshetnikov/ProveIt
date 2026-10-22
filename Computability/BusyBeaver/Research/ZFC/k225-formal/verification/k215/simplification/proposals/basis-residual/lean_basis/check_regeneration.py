#!/usr/bin/env python3
"""Check the synchronized producer in an isolated, source-pinned input tree."""
from pathlib import Path
import argparse, hashlib, json, shutil, subprocess, sys

HERE=Path(__file__).resolve().parent
PIN='57541fe0cfe3af62b4cb58747d8d1d7c16b338d5'
REL=Path('Computability/BusyBeaver/Research/ZFC/k225-formal')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',required=True,type=Path)
    ap.add_argument('--out',required=True,type=Path)
    a=ap.parse_args();repo=a.repo.resolve();out=a.out.resolve()
    assert not out.exists(),'Use a new output directory'
    head=subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
    assert head==PIN,(head,PIN)
    out.mkdir(parents=True);stage=out/'inputs';stage.mkdir();overlay=HERE/'repo_overlay'/REL
    files=['generate_dominated_implication_lean.py','dominated_implication_templates/basis.txt',
        'dominated_implication_templates/adapter.txt','rho8cd/derivation_core.txt',
        'verification/k215/simplification/phase10/upstream-merge/source-review/inputs/DominatedImplication.upstream.lean']
    inputs={}
    for name in files:
        source=overlay/name if (overlay/name).exists() else repo/REL/name
        if not (overlay/name).exists():
            assert source.read_bytes()==subprocess.check_output(['git','-C',str(repo),'show',head+':'+(REL/name).as_posix()])
        target=stage/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target);inputs[name]=sha(target)
    command=[sys.executable,str(stage/'generate_dominated_implication_lean.py'),'--out',str(out/'generated')]
    r=subprocess.run(command,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (out/'producer.log').write_text(r.stdout);assert r.returncode==0,r.stdout
    expected={'DominatedImplication.lean':HERE/'BusyBeaver/ZFC/DominatedImplication.lean',
        'DomRho8.lean':repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DomRho8.lean'}
    outputs={}
    for name,src in expected.items():
        target=out/'generated/BusyBeaver/ZFC'/name
        assert src.read_bytes()==target.read_bytes(),name
        outputs[name]=sha(target)
    record={'status':'PASS','source_commit':head,'inputs':inputs,'outputs':outputs,
        'producer_report':json.loads(r.stdout),'proof_scope':'Regeneration diagnostic; use Lean kernel check for proof validity.'}
    (out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))
if __name__=='__main__':main()
