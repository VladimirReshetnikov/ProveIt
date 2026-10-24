#!/usr/bin/env python3
"""Check literal integer translation bijections, independently of producer."""
import argparse,copy,hashlib,json
from pathlib import Path
from audit_literal_independent import read,need,collect,serial,normrow,substitute,sos,metrics
from audit_signed_independent import filehash,add,var,const

def audit(srcdir,dstdir):
    src=read(srcdir/'equation.json');tar=read(dstdir/'equation.json');cert=read(dstdir/'translation_certificate.json')
    need(src['domain']==tar['domain']=='unrestricted integers','translation requires Z')
    need(filehash(src)==cert['input_sha256'] and filehash(tar)==cert['output_sha256'],'translation hash')
    need(cert['convention']=='old_coordinate = new_coordinate + shift' and cert['inverse']=='new_coordinate = old_coordinate - shift','translation convention')
    shifts=cert['shifts'];need(all(type(v)==int and type(c)==int and 0<=v<len(src['variables']) for v,c in shifts),'nonintegral/out-of-range shift')
    need(len({v for v,c in shifts})==len(shifts),'duplicate shift')
    images={v:add(var(v),const(c)) for v,c in shifts};inverse={v:add(var(v),const(-c)) for v,c in shifts}
    need(len(src['residuals'])==len(tar['residuals']) and src['variables']==tar['variables'],'translation changed coordinates/rows')
    for old,new in zip(src['residuals'],tar['residuals']):
        need(old['label']==new['label'],'translation label')
        need(substitute(normrow(old),images)==normrow(new),'forward polynomial translation')
        need(substitute(normrow(new),inverse)==normrow(old),'inverse polynomial translation')
    expected=copy.deepcopy(src);expected.pop('metrics',None);expected.pop('elimination',None);expected['variant']+=':integral_translation';expected['residuals']=tar['residuals']
    need(expected==tar,'unexpected metadata change')
    p=sos(tar);need(p==collect(read(dstdir/'expanded_polynomial.json')['terms']),'translated SOS coefficient mismatch')
    return metrics(tar,p)|{'translated_coordinates':len(shifts),'bijection':'Coordinatewise integral translation with verified inverse; no domain restriction is introduced.','verified':True,'sha256':{str(f):hashlib.sha256(f.read_bytes()).hexdigest() for b in [srcdir,dstdir] for f in b.glob('*.json')}}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('target',type=Path);p.add_argument('--output',type=Path,required=True);a=p.parse_args();r=audit(a.source,a.target);a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='sha256'},indent=2))
