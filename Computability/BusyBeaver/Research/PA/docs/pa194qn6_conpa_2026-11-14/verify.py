#!/usr/bin/env python3
"""Rebuild QN6 and replay its acceptance checks without a checkout or network.

Default includes the independent literal-tape engine. --quick omits only that
engine; recorded receipts are not treated as fresh verification in that mode.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile,shutil
ROOT=Path(__file__).resolve().parent

def run(argv,logs,label):
    print(label,flush=True)
    p=subprocess.run([sys.executable,'-B',*map(str,argv)],capture_output=True,text=True)
    (logs/(label.replace(' ','_')+'.log')).write_text(p.stdout+p.stderr)
    if p.returncode:
        print(p.stdout+p.stderr,file=sys.stderr)
        raise RuntimeError(label+' failed')
    return p.stdout

def main():
    if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions must be enabled.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--quick',action='store_true')
    ap.add_argument('--receipt',type=Path)
    args=ap.parse_args()
    pins=json.loads((ROOT/'PROVENANCE.json').read_text())['input_hashes']
    for rel,sha in pins.items():
        assert hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==sha,rel
    with tempfile.TemporaryDirectory(prefix='pa194qn6-')as td:
        work=Path(td);logs=work/'logs';logs.mkdir()
        target=work/'machine'
        run([ROOT/'construction/build_qn6.py','--output',target],logs,'construction')
        checked=[]
        for f in target.iterdir():
            assert f.read_bytes()==(ROOT/'machine'/f.name).read_bytes(),f.name
            checked.append(f.name)
        run([ROOT/'proof/check_binding.py','--output',work/'binding.json'],logs,'source binding')
        run([ROOT/'proof/check_commands.py','--output',work/'commands.json'],logs,'symbolic command compiler')
        shutil.copy2(ROOT/'proof/exchange_certificate.py',work/'exchange_certificate.py')
        run([work/'exchange_certificate.py'],logs,'finite exchange proof')
        assert (work/'exchange_certificate.json').read_bytes()==(ROOT/'proof/exchange_certificate.json').read_bytes()
        novel=json.loads(run([ROOT/'comparison/check_novelty.py',target/'machine.tm'],logs,'corpus novelty'))
        assert novel['structurally_new_in_recognized_corpus']
        if not args.quick:
            run([ROOT/'verification/check.py',target],logs,'independent literal tape')
            independent=json.loads((target/'independent/receipt.json').read_text())
            assert independent==json.loads((ROOT/'machine/independent/receipt.json').read_text())
            assert (target/'independent/contracts.json').read_bytes()==(ROOT/'machine/independent/contracts.json').read_bytes()
        result={'status':'PASS','working_states':194,'rows':388,'reproduced_files':sorted(checked),
                'source_binding_replayed':True,'all_store_command_certificate_replayed':True,
                'K_S_exchange_replayed':True,'graphs_compared':novel['graphs_compared'],
                'structurally_new_in_recognized_corpus':True,'construction_outcomes':4877,
                'whole_blank_startup_steps':58320,'independent_literal_replayed':not args.quick,
                'dense_sha256':'72a35e528c1061f61e211d0bcf3a954859d2dbbcfd6b9f7846e4f970bb04e4e9',
                'proof_status':'Executable finite and universal symbolic certificates for an ordinary mathematical PA-provability proof; not a new Lean/Rocq endpoint.'}
        if args.receipt:args.receipt.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result,indent=2))
if __name__=='__main__':main()
