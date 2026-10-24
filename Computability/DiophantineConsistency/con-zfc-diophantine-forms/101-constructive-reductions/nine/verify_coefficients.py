#!/usr/bin/env python3
"""Replay the retained finite coefficient recipes and compare whole integers."""
from pathlib import Path
import gzip,hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parent

def need(ok,m):
    if not ok:raise ValueError(m)
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);out=importlib.util.module_from_spec(spec);spec.loader.exec_module(out);return out

def compare(values,base):
    out=[]
    for name,value in values.items():
        actual=gzip.decompress((base/'data'/f'{name}.bin.gz').read_bytes())
        raw=value.to_bytes((value.bit_length()+7)//8,'little')
        need(actual==raw,'whole coefficient bytes '+name)
        out.append(dict(port=name,bits=value.bit_length(),raw_bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),equal=True))
    return out

def main():
    source=ROOT/'native_original31/build_coefficients.py';m=module('retained_original31',source)
    data=m.recipe();_,_,_,support,mask,dc,targets,pads=data
    B=1<<m.D;DC=sum(c<<(m.BITS*e) for e,c in dc.items());DR=1<<(m.BITS*m.H)
    MF0=4+(mask<<(m.BITS*m.T1))+(mask<<(m.BITS*m.T2))
    MF0+=sum(1<<(m.BITS*t) for t,*_ in targets)+sum(c<<(m.BITS*e) for e,c in pads.items())
    MC=B-1-sum(1<<(m.BITS*e) for e in support if e!=1)-(2<<(m.BITS*1063))
    old=dict(beta=B-1,K=DC+B*DR,MC=MC,MF_source=MF0+B-1)
    old_receipt=compare(old,ROOT)
    source2=ROOT/'compact/provenance/verify_one_page_tuple54.py';u=module('retained_compact54',source2)
    seed=(ROOT/'compact/coefficients/COMPACT54_SEED.txt').read_bytes()
    need(hashlib.sha256(seed).hexdigest()==u.SEED_SHA256,'literal compact seed')
    values,actions,modes,rank=u.construct(int(seed))
    compact_receipt=compare(values,ROOT/'compact')
    for r in compact_receipt:need(r['sha256']==u.EXPECTED[r['port']],'authoritative compact value')
    result=dict(status='PASS',original31=old_receipt,compact54=compact_receipt,
                original_recipe_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                compact_recipe_sha256=hashlib.sha256(source2.read_bytes()).hexdigest(),
                compact_seed_sha256=hashlib.sha256(seed).hexdigest(),
                scope='Finite actual numeral reconstruction from literal machine/tile input. No new unbounded compiler/calculus theorem is asserted.')
    (ROOT/'COEFFICIENT_RECONSTRUCTION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','original31_ports':4,'compact54_ports':4,'exact_whole_byte_comparisons':8},indent=2))
if __name__=='__main__':main()
