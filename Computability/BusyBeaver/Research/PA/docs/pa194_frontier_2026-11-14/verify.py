#!/usr/bin/env python3
"""Replay the two new constructions and exact comparison offline."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
def main():
    if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions must remain enabled')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path)
    a=ap.parse_args();out=a.output or Path(tempfile.mkdtemp(prefix='pa194-replay-'))
    out.mkdir(parents=True,exist_ok=True)
    if out.resolve()==ROOT or ROOT in out.resolve().parents:raise ValueError('Choose output outside the frozen package')
    results={}
    for folder in ['AX11G','GH']:
        print('Replaying',folder,flush=True)
        with (out/f'{folder}.log').open('w') as log:
            subprocess.run([sys.executable,'-B',str(ROOT/'machines'/folder/'verify.py'),'--output',str(out/f'{folder}.json')],check=True,stdout=log,stderr=subprocess.STDOUT)
        results[folder]=json.loads((out/f'{folder}.json').read_text())
    novelty=out/'novelty.json'
    tables=[ROOT/'machines'/f/'machine/machine.tm' for f in ['AX11G','GH']]
    with (out/'novelty.log').open('w') as log:
        subprocess.run([sys.executable,'-B',str(ROOT/'comparison/check_frontier_novelty.py'),*map(str,tables),'--output',str(novelty)],check=True,stdout=log)
    n=json.loads(novelty.read_text())
    assert all(x['structurally_new_in_recognized_scope'] for x in n['candidate_results'])
    assert len({x['strong_canonical_sha256'] for x in n['candidate_results']})==2
    subprocess.run([sys.executable,'-B',str(ROOT/'search/tags/milp/verify_dictionaries.py')],check=True)
    if (ROOT/'SHA256SUMS').exists():
        for line in (ROOT/'SHA256SUMS').read_text().splitlines():
            expected,name=line.split('  ',1)
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==expected,name
    receipt={'status':'PASS','candidates':list(results),'novelty':n,'unconditional_ipra_calibration':False}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('PASS:',out/'receipt.json')
if __name__=='__main__':main()
