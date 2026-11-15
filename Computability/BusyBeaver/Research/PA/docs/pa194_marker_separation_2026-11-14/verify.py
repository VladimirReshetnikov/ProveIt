#!/usr/bin/env python3
"""Offline release checks; --full-parent additionally replays the inherited physical certificates."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile,zipfile

ROOT=Path(__file__).resolve().parent
NAMES=('PA194LCGMS','PA194LCGSMS')

def main():
    assert __debug__ and not sys.flags.optimize,'Run without Python -O.'
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--full-parent',action='store_true')
    a=ap.parse_args()
    out=a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='pa194-ms-replay-'))
    out.mkdir(parents=True,exist_ok=True)
    if out==ROOT or ROOT in out.parents:raise ValueError('Replay output must be outside the frozen release.')
    manifest=json.loads((ROOT/'MANIFEST.sha256.json').read_text())
    for name,digest in manifest.items():
        p=Path(name)
        assert not p.is_absolute() and '..' not in p.parts
        assert hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==digest,name
    def run(name,args):
        with (out/(name+'.log')).open('w') as log:
            subprocess.run([sys.executable,'-B',*map(str,args)],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
    run('build',[ROOT/'build.py','--output',out/'machines'])
    for name in NAMES:
        for file in ('machine.tm','machine.native.tm','labels.json'):
            assert (out/'machines'/name/file).read_bytes()==(ROOT/'machines'/name/file).read_bytes(),(name,file)
    run('independent',[ROOT/'verification/independent.py','--package',ROOT,'--output',out/'independent.json'])
    run('novelty',[ROOT/'comparison/check_novelty.py','--census',ROOT/'comparison/census.json','--output',out/'novelty.json',*[ROOT/'machines'/n/'machine.tm' for n in NAMES]])
    novelty=json.loads((out/'novelty.json').read_text())
    assert novelty['prior_spanning194_classes']==520
    assert all(r['new_within_recognized_corpus'] for r in novelty['results'])
    if a.full_parent:
        archive=ROOT/'references/pa194_loop_return_2026-11-14.zip'
        parent=out/'parent'
        with zipfile.ZipFile(archive) as z:
            for name in z.namelist():
                p=Path(name)
                assert not p.is_absolute() and '..' not in p.parts,name
            z.extractall(parent)
        run('parent_full',[parent/'pa194_loop_return_2026-11-14/reproduce.py','--full','--out',out/'parent_replay'])
        assert json.loads((out/'parent_replay/summary.json').read_text())['status']=='PASS'
    result={'status':'PASS','machines':list(NAMES),'manifest_files':len(manifest),
        'literal_tables_reconstructed_and_byte_compared':True,'independent_local_and_startup_audit':True,
        'prior_spanning194_classes':520,'new_and_mutually_distinct':True,
        'full_parent_replay_this_invocation':a.full_parent,
        'proof_scope':'Finite bindings for the written iPRA relative theorem. Absolute Con(PA) calibration is the explicitly inherited written proof, not a new Lean kernel endpoint.',
        'output':str(out)}
    (out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
