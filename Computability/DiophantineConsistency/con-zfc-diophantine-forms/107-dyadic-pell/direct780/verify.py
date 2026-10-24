#!/usr/bin/env python3
"""Authenticate, independently check, rebuild, and test rejection controls."""
from pathlib import Path
import argparse,copy,hashlib,json,subprocess,sys,tempfile,zipfile
import check
ROOT=Path(__file__).resolve().parent

def need(ok,message):
    if not ok:raise ValueError(message)
def load(p):return json.loads(p.read_text())
def run(script,*args):
    command=[sys.executable]+(['-O'] if not __debug__ else [])+[str(ROOT/script),*map(str,args)]
    result=subprocess.run(command,text=True,capture_output=True,check=True)
    return json.loads(result.stdout)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--receipt',type=Path)
    args=ap.parse_args()
    result=run('check.py')
    rebuilt=[]
    with tempfile.TemporaryDirectory(prefix='direct780-rebuild-') as name:
        out=Path(name)
        run('build.py','--output',out)
        run('check.py','--equations',out)
        for file in sorted((ROOT/'equations').glob('*.json')):
            need((out/file.name).read_bytes()==file.read_bytes(),'byte reproduction '+file.name)
            rebuilt.append(file.name)

    eq=load(ROOT/'upstream/source690/equation.json')
    raw=load(ROOT/'upstream/source690/gate_ledger.json')
    interface=load(ROOT/'upstream/source690/interface.json')
    macros=load(ROOT/'upstream/source690/macro_inventory.json')
    p=ROOT/'equations';domain=load(p/'domain_certificate.json')
    signed=load(p/'signed_source.json');projection=load(p/'projection.json')
    output=load(p/'equation.json');expanded=load(p/'expanded_polynomial.json')
    rejected=[]
    def reject(name,operation):
        try:operation()
        except ValueError as exc:rejected.append({'name':name,'rejection':str(exc)})
        else:raise ValueError('corruption was accepted: '+name)
    changed=copy.deepcopy(domain);changed['guards'].pop(0)
    reject('missing_guard',lambda:check.check_domain(eq,changed,raw,interface,macros))
    changed=copy.deepcopy(domain);changed['power_facts'][0][1]=1
    reject('unproved_strict_power_quotient_sign',lambda:check.check_domain(eq,changed,raw,interface,macros))
    changed=copy.deepcopy(interface);changed['frame']['norm_row']=changed['frame']['D_row']
    reject('wrong_frame_identity',lambda:check.check_domain(eq,domain,raw,changed,macros))
    changed=copy.deepcopy(interface);changed['powers'][0]['X']=changed['powers'][1]['X']
    reject('wrong_power_index_pair',lambda:check.check_domain(eq,domain,raw,changed,macros))
    changed=copy.deepcopy(projection);changed['steps'][0]['restoration'][0][0]+=1
    reject('wrong_restoration_coefficient',lambda:check.check_projection(eq,signed,changed,output,expanded,domain))
    changed=copy.deepcopy(expanded);changed['terms'][0][0]+=1
    reject('wrong_expanded_coefficient',lambda:check.check_projection(eq,signed,projection,output,changed,domain))

    # Verify the comparison inventory directly against the immutable parent.
    with zipfile.ZipFile(ROOT/'upstream/ConZFC_407_888_Quartics_2026-10-24.zip') as z:
        original=json.loads(z.read('ConZFC_407_888_Quartics/equations/integer888/domain_conversion.json'))
    old,new={g['variable'] for g in original['guards']},set(domain['guards'])
    need(new<=old and len(old-new)==36,'guard reduction count')
    changes=load(ROOT/'certificates/guard_changes.json')
    need(changes['removed']==[{'index':v,'name':eq['variables'][v]['name']} for v in sorted(old-new)],'guard comparison inventory')

    receipt={'status':'PASS','optimized_python':not __debug__,
             'independent_check':result,'byte_reproduced_files':rebuilt,
             'rejected_corruptions':rejected,
             'delivered_polynomial_sha256':hashlib.sha256((p/'expanded_polynomial.json').read_bytes()).hexdigest(),
             'scope':'Exact finite instance and rejection audit; the universal mathematical proof is PROOF.md.'}
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt,indent=2,sort_keys=True))

if __name__=='__main__':main()
