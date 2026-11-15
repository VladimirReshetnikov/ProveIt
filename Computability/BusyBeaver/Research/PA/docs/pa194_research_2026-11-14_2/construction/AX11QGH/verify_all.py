#!/usr/bin/env python3
"""Rebuild and replay the exact PA194AX11QGH certificate, offline.

Full mode rebuilds the table, rechecks all source contracts, checks the
abstract command equations, and reruns the independent literal-tape engine.
Quick mode explicitly skips both per-site symbolic tape replays.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile

HERE=Path(__file__).resolve().parent
DENSE_SHA='513e9c8b28e0dd41e6003bb8d82c80ff3dac5fb3c5274cd2f709a3bba8c3e9e1'

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
    assert __debug__ and not sys.flags.optimize,'Run without -O.'
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--quick',action='store_true')
    ap.add_argument('--receipt',type=Path,default=HERE/'evidence/replay_receipt.json')
    a=ap.parse_args()
    manifest=json.loads((HERE/'INPUT_SHA256.json').read_text())
    for name,digest in manifest.items():assert sha(HERE/name)==digest,name
    assert sha(HERE/'machine/machine.tm')==DENSE_SHA
    with tempfile.TemporaryDirectory(prefix='pa194ax11qgh-') as temporary:
        temp=Path(temporary)
        def run(name,args):
            with (temp/(name+'.log')).open('w') as log:
                result=subprocess.run([sys.executable,'-B',*map(str,args)],cwd=HERE,
                                      stdout=log,stderr=subprocess.STDOUT)
            if result.returncode:
                print((temp/(name+'.log')).read_text(),file=sys.stderr)
                raise RuntimeError(name+' failed')
            print(name+': PASS',flush=True)
        buildargs=[HERE/'build.py','--output',temp/'machine']
        if a.quick:buildargs.append('--quick')
        run('construction',buildargs)
        for name in ['machine.tm','machine.native.tm','raw.native.tm','labels.json',
                     'nodes.json','grammar.tree.json','grammar.json','sites.json',
                     'instructions.json','folds.json','local_folds.json','fixed_patch.json']:
            assert (temp/'machine'/name).read_bytes()==(HERE/'machine'/name).read_bytes(),name
        run('commands',[HERE/'check_commands.py','--machine',temp/'machine',
                        '--output',temp/'commands.json'])
        commands=json.loads((temp/'commands.json').read_text())
        assert commands['status']=='PASS'
        run('physical_closure',[HERE/'physical_ipra_audit.py','--bundle',HERE,
                               '--output',temp/'physical_closure.json'])
        closure=json.loads((temp/'physical_closure.json').read_text())
        assert closure['status']=='PASS'
        construction=json.loads((temp/'machine/receipt.json').read_text())
        independent=None
        if not a.quick:
            run('independent',[HERE/'independent/check.py',temp/'machine',
                               '--output',temp/'independent'])
            independent=json.loads((temp/'independent/PA194AX11QGH/receipt.json').read_text())
            old=json.loads((HERE/'evidence/independent/PA194AX11QGH/receipt.json').read_text())
            for key in ['source_sites','source_outcomes','symbolic_steps',
                        'maximum_symbolic_steps','minimum_positive_duration_constant',
                        'dense_sha256','native_sha256','contracts_sha256']:
                assert independent[key]==old[key],key
        receipt=dict(status='PASS',family='PA194AX11QGH',working_states=194,
                     dense_sha256=DENSE_SHA,source_sites=3671,source_outcomes=4778,
                     construction=construction['runtime'],
                     command_equations='PASS',physical_frame_closure=closure,
                     independent_literal_replay=independent,
                     quick_mode=a.quick,per_site_symbolic_replays_skipped=a.quick,
                     kernel_checked=False)
        a.receipt.parent.mkdir(parents=True,exist_ok=True)
        a.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
