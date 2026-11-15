#!/usr/bin/env python3
"""Offline replay of the complete research release. No third-party packages."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent

def run(name,args,out):
    print('Running',name,flush=True)
    r=subprocess.run([sys.executable,'-B',*map(str,args)],cwd=ROOT,text=True,
                     stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (out/(name+'.log')).write_text(r.stdout)
    if r.returncode:
        print(r.stdout)
        raise SystemExit(name+' failed')

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path)
    p.add_argument('--quick',action='store_true',help='Skip the complete literal/source replay; retain integrity, novelty, incoming startup, and congruence checks.')
    a=p.parse_args()
    if not __debug__:raise SystemExit('Run without Python -O.')
    out=(a.output or Path(tempfile.mkdtemp(prefix='pa194-joint-'))).resolve()
    if out==ROOT or ROOT in out.parents:
        raise SystemExit('Choose an output directory outside this frozen release.')
    out.mkdir(parents=True,exist_ok=True)
    manifest=json.loads((ROOT/'MANIFEST.sha256.json').read_text())
    for name,expected in manifest['files'].items():
        raw=(ROOT/name).read_bytes()
        if hashlib.sha256(raw).hexdigest()!=expected:raise AssertionError('Hash mismatch: '+name)
    for name,folder in [('PA194ORMP','machine'),('PA194ORMPLC3','accelerated')]:
        assert (ROOT/(name+'.tm')).read_bytes()==(ROOT/'construction'/folder/'machine.tm').read_bytes()
    if not a.quick:
        run('construction_and_literal_replay',[ROOT/'construction/reproduce.py','--output',out/'construction'],out)
    run('novelty',[ROOT/'comparison/check_novelty.py',ROOT/'PA194ORMP.tm',ROOT/'PA194ORMPLC3.tm','--output',out/'novelty.json'],out)
    run('incoming_startups',[ROOT/'comparison/verify_incoming_startups.py','--output',out/'incoming_startups.json'],out)
    run('ordinary_congruences',[ROOT/'comparison/verify_congruences.py','--output',out/'congruences.json'],out)
    run('json_supplement',[ROOT/'comparison/verify_json_supplement.py','--output',out/'json_supplement.json'],out)
    result={'status':'PASS','manifest_files':len(manifest['files']),
            'complete_literal_replay':not a.quick,
            'candidates':['PA194ORMP','PA194ORMPLC3'],
            'scope':'Reproducible finite and symbolic evidence accompanying the written relative iPRA proof; not an end-to-end Lean kernel build.'}
    (out/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
