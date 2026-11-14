#!/usr/bin/env python3
"""Offline reproduction of the PA194AX11QH construction and certificates.
The default reruns both physical engines. This does not prove Con(PA) calibration.
"""
from pathlib import Path
import argparse,json,subprocess,sys,tempfile,hashlib
ROOT=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--quick',action='store_true',help='Skip only independent literal-tape replay; still rebuild and run construction source contracts.')
    p.add_argument('--receipt',type=Path)
    a=p.parse_args();assert __debug__ and not sys.flags.optimize,'Run without -O.'
    with tempfile.TemporaryDirectory(prefix='pa194ax11qh-verify-') as tmp:
        tmp=Path(tmp);machine=tmp/'machine'
        stages=[]
        def run(stage,args):
            process=subprocess.run([sys.executable,'-B',*map(str,args)],cwd=ROOT,text=True,capture_output=True)
            if process.returncode:
                print(process.stdout);print(process.stderr,file=sys.stderr);raise SystemExit(process.returncode)
            stages.append(stage);print(stage+': PASS',flush=True)
        run('construction',[ROOT/'build.py','--output',machine])
        for name in ('machine.tm','machine.native.tm','raw.native.tm'):
            assert (machine/name).read_bytes()==(ROOT/'machine'/name).read_bytes(),name
        for name in ('labels.json','nodes.json','grammar.json','grammar.tree.json','sites.json','instructions.json','folds.json','local_fold_cases.json'):
            assert json.loads((machine/name).read_text())==json.loads((ROOT/'machine'/name).read_text()),name
        run('independent source binding',[ROOT/'proof/check_binding.py','--machine',machine,'--output',tmp/'source.json'])
        run('symbolic emitter and command identities',[ROOT/'proof/check_commands.py','--machine',machine,'--output',tmp/'commands.json'])
        # Run the unchanged finite exchange construction in an isolated directory.
        exchange=tmp/'exchange_certificate.py';exchange.write_bytes((ROOT/'proof/exchange_certificate.py').read_bytes())
        run('premise-exchange certificate',[exchange])
        assert json.loads((tmp/'exchange_certificate.json').read_text())==json.loads((ROOT/'proof/exchange_certificate.json').read_text())
        independent=None
        if not a.quick:
            run('independent literal-tape replay',[ROOT/'verification/check_literal.py','--machine',machine,'--output',tmp/'independent'])
            independent=json.loads((tmp/'independent/receipt.json').read_text())
            assert independent==json.loads((ROOT/'machine/independent/receipt.json').read_text())
        receipt={'status':'PASS','family':'PA194AX11QH','stages':stages,
                 'independent_literal_replay_performed':not a.quick,
                 'source_sites':3671,'source_outcomes':4778,'working_states':194,
                 'startup_steps':57922,'dense_sha256':hashlib.sha256((machine/'machine.tm').read_bytes()).hexdigest(),
                 'ipra_consistency_equivalence_proved':False,
                 'scope':'Reproducible finite/symbolic checks; baseline PA-to-numerical-calculus calibration and iPRA internalization are separate obligations.'}
        if a.receipt:a.receipt.parent.mkdir(parents=True,exist_ok=True);a.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps(receipt,indent=2),flush=True)
if __name__=='__main__':main()
