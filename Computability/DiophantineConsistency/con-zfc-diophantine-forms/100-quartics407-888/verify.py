#!/usr/bin/env python3
"""Independent algebra checks plus full deterministic coefficient regeneration.

No consistency search, network request, or third-party Python package is used.
Delivered equations are read only. Optional receipts are written separately.
"""
from pathlib import Path
from copy import deepcopy
import argparse,hashlib,importlib.util,json,sys,tempfile
import reproduce

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import audit_new,source_identity
sys.path.insert(0,str(ROOT/'code/integer_pipeline'))
from verify_integer import domain
from verify_projection import verify as integer_projection
from independent_polynomial import verify_expansion
spec=importlib.util.spec_from_file_location('independent_natural_checker',ROOT/'code/psd_contract/check.py')
natural=importlib.util.module_from_spec(spec);spec.loader.exec_module(natural)

def need(ok,message):
    if not ok:raise ValueError(message)
def read(path):return json.loads(Path(path).read_text())
def normalize(x):return json.loads(json.dumps(x,sort_keys=True))

def exponent_ledger(cert):
    weights={i:1 for i in range(len(cert['inputs']))}
    def w(atom):
        kind,value=atom
        return max(0,(value-1).bit_length()) if kind=='c' else weights[value]
    for row in cert['gates']:
        a,b=w(row['left']),w(row['right'])
        expected=max(a,b)+1 if row['operation']=='add' else a+b
        need(row['operation'] in ('add','mul') and row['exponent']==expected,'majorant recurrence')
        need(row['output'] not in weights,'majorant repeated output')
        weights[row['output']]=expected
    e=w(cert['output']);need(e==cert['exponent'],'majorant output')
    emitted=cert.get('carrier_exponent',cert.get('emitted_exponent'))
    need(emitted>=e and emitted&(emitted-1)==0,'majorant emitted power')
    return {'gates':len(cert['gates']),'computed_exponent':e,'emitted_exponent':emitted}

def natural_audit(source,d):
    target=read(d/'equation.json');cert=read(d/'elimination_certificate.json')
    receipt,terms=natural.verify(source,target,cert)
    need(terms==read(d/'expanded_polynomial.json')['terms'],'natural expanded coefficients')
    i=next(i for i,s in enumerate(cert['steps']) if s['nonnegative_certificate']['squares'])
    for mode in ('alter','negative'):
        bad=deepcopy(cert);weight=bad['steps'][i]['nonnegative_certificate']['squares'][0]['weight']
        weight[0]=weight[0]+weight[1] if mode=='alter' else -abs(weight[0])
        try:natural.verify(source,target,bad)
        except ValueError:pass
        else:raise ValueError('corrupted natural certificate accepted')
    receipt['corrupt_nonnegative_certificates_rejected']=True
    return receipt

def integer_audit(source,d):
    need(read(d/'source_natural.json')==source,'integer parent differs')
    signed=read(d/'guarded.json');conversion=read(d/'domain_conversion.json')
    target=read(d/'equation.json');cert=read(d/'elimination_certificate.json')
    receipt={'domain':domain(source,signed,conversion),
             'projection':integer_projection(signed,target,cert),
             'expansion':verify_expansion(target,read(d/'expanded_polynomial.json'))}
    bad=deepcopy(conversion);bad['positivity']['proof_steps'][0]['rhs'][0][0]+=1
    try:domain(source,signed,bad)
    except ValueError:receipt['corrupt_sign_certificate_rejected']=True
    else:raise ValueError('corrupted sign inference accepted')
    return receipt

def main(receipt_path=None):
    upstream=read(ROOT/'provenance/UPSTREAM_SHA256.json')
    for name,digest in upstream.items():
        need(hashlib.sha256((ROOT/'upstream'/name).read_bytes()).hexdigest()==digest,'upstream content changed: '+name)
    b,source,poly,metrics,raw=reproduce.source_data()
    for name,value in reproduce.source_files(b,source,poly,metrics,raw).items():
        need(normalize(value)==read(ROOT/'equations/source690'/name),'source artifact regeneration: '+name)
    need(normalize(raw)==read(ROOT/'provenance/projected_raw_audit_input.json'),'raw arithmetic ledger regeneration')
    raw=normalize(raw)
    audit=audit_new.Audit(raw).run();audit.update(audit_new.fixtures())
    bad=deepcopy(raw);bad['radix']['radix']=['c',1]
    try:audit_new.Audit(bad).run()
    except ValueError:audit['corrupt_radix_rejected']=True
    else:raise ValueError('corrupted radix accepted')
    results={'status':'PASS','python_optimized':not __debug__,
             'upstream_files_authenticated':len(upstream),
             'source':metrics,'source_identity':source_identity.check(),
             'label_majorant':exponent_ledger(raw['label_majorant']),
             'local_majorant':exponent_ledger(raw['local_majorant']),
             'arithmetic':audit,'equations':{}}
    for name in ('natural407','natural410'):
        results['equations'][name]=natural_audit(source,ROOT/'equations'/name)
    for name in ('integer888','integer917'):
        results['equations'][name]=integer_audit(source,ROOT/'equations'/name)
    # Reproduce all final lists and certificates in isolation, then compare
    # parsed exact data. This also validates the delivered producer paths.
    with tempfile.TemporaryDirectory(prefix='con-zfc-replay-') as tmp:
        reproduce.generate(tmp)
        for name in ('natural407','natural410','integer888','integer917'):
            filenames=['equation.json','expanded_polynomial.json','elimination_certificate.json']
            if name.startswith('integer'):filenames+=['domain_conversion.json','guarded.json']
            for filename in filenames:
                need(read(Path(tmp)/name/filename)==read(ROOT/'equations'/name/filename),
                     'full coefficient replay differs: '+name+'/'+filename)
    results['complete_regeneration']='PASS'
    results['scope']='Exact finite algebra and regeneration; universal proofs and inherited C222/Pell calibration are specified in report.tex.'
    if receipt_path:
        receipt_path=Path(receipt_path);receipt_path.parent.mkdir(parents=True,exist_ok=True)
        receipt_path.write_text(json.dumps(results,sort_keys=True,indent=2)+'\n')
    print(json.dumps(results,sort_keys=True,indent=2))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--receipt',type=Path)
    args=parser.parse_args();main(args.receipt)
