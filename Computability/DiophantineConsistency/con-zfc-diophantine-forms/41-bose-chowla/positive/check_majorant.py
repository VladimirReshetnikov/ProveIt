#!/usr/bin/env python3
"""Finite checks, not an end-to-end Con(ZFC) verification."""
import argparse, gzip, hashlib, json, random
from pathlib import Path
import numpy as np
from build_majorant import build,evaluate,VARIABLES,PORTS

def radical_mul(a,b,rad,p):
    out=[0]*8
    for x in range(8):
        for y in range(8):
            k=x&y;v=a[x]*b[y]
            for j in range(3):
                if k&(1<<j):v*=rad[j]
            out[x^y]=(out[x^y]+v)%p
    return out

def direct_norm(e,p):
    out=[1]+[0]*7;rad=[e['A'],e['G'],e['D']]
    for sa in [-1,1]:
      for sg in [-1,1]:
       for sf in [-1,1]:
        lin=[e['W'], -sa*e['HM'], -sg*e['L'],0,0,0,0,0]
        f=[e['d']*x%p for x in radical_mul(lin,lin,rad,p)]
        f[0]=(f[0]-e['H2']*(e['Q']*(e['D']*e['v2']+e['b']**2)-1))%p
        f[4]=(f[4]+sf*e['H2']*2*e['Q']*e['v']*e['b'])%p
        out=radical_mul(out,f,rad,p)
    assert all(x==0 for x in out[1:]),out
    return out[0]

def poly_eval(packet,vals,p):
    def trim(a):
        nz=np.flatnonzero(a)
        return a[:nz[-1]+1] if len(nz) else np.array([0],dtype=np.int64)
    e={v:np.array([0,vals[v]%p],dtype=np.int64) for v in VARIABLES}
    e.update({v:np.array([vals[v]%p],dtype=np.int64) for v in PORTS})
    for n,op,x,y in packet['source']:
        x=np.array([x%p],dtype=np.int64) if isinstance(x,int) else e[x]
        y=np.array([y%p],dtype=np.int64) if isinstance(y,int) else e[y]
        if op=='*':z=np.convolve(x,y)%p
        else:
            z=np.zeros(max(len(x),len(y)),dtype=np.int64);z[:len(x)]=x
            z[:len(y)]+=y if op=='+' else -y
            z%=p
        e[n]=trim(z)
    return e

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--data-dir',type=Path,default=Path(__file__).resolve().parent.parent/'upstream/source31/signed10/data')
    args=parser.parse_args()
    rng=random.Random(20261023);packet=build();checks=0
    dest=Path(__file__).resolve().parent
    assert packet['operations']==len(packet['source'])==122
    assert (dest/'positive12_majorant_product.json').read_text()==json.dumps(packet,indent=2)+'\n'
    system=dict(packet);system.pop('output');system['source']=packet['source'][:-5]
    system['comparisons']=[['Nk',1],['Nt',1],['term1','term2']]
    system['exact_degree']=929;system['operations']=len(system['source'])
    assert system['operations']==117
    assert (dest/'positive12_majorant_system.json').read_text()==json.dumps(system,indent=2)+'\n'
    binding=json.loads(Path(__file__).with_name('COEFFICIENT_BINDING.json').read_text())
    values_by_name={};bound_files=[]
    for f in binding['files']:
        compressed=(args.data_dir/(f['name']+'.bin.gz')).read_bytes()
        raw=gzip.decompress(compressed)
        assert hashlib.sha256(compressed).hexdigest()==f['gzip_sha256']
        assert hashlib.sha256(raw).hexdigest()==f['sha256']
        value=int.from_bytes(raw,'little')
        assert len(raw)==f['bytes'] and value.bit_length()==f['bit_length']
        values_by_name[f['name']]=value;bound_files.append(f['name'])
    actual_ports={port:values_by_name[name] for port,name in binding['port_aliases'].items()}
    for p in [10007,10009,10037]:
        for case in range(40):
            vals={v:rng.randrange(p) for v in VARIABLES+PORTS}
            e=evaluate(packet,vals,p)
            assert direct_norm(e,p)==e['N']
            checks+=1
    rays=[]
    for p in [10007,10009,10037]:
        vals={v:rng.randrange(1,p) for v in VARIABLES+PORTS}
        es=poly_eval(packet,vals,p)
        assert len(es['N'])-1==929
        assert len(es['polynomial'])-1==938
        q0=vals['beta']*vals['J']%p;k0=(vals['eta']+vals['zeta'])%p
        lead=-pow(2,46,p)
        for x,a in [(vals['i'],43),(k0,103),(vals['T'],5),(vals['s'],152),((vals['w']+q0)%p,69),(q0,549),((q0-vals['F'])%p,8)]:
            lead=lead*pow(x,a,p)%p
        assert lead==int(es['N'][-1]),(lead,es['N'][-1])
        rays.append({'prime':p,'norm_degree':929,'product_degree':938,'leading_coefficient':lead})
    actual_rays=[]
    for p in [10007,10009,10037]:
        vals={v:rng.randrange(1,p) for v in VARIABLES};vals.update({v:n%p for v,n in actual_ports.items()})
        e=evaluate(packet,vals,p)
        assert direct_norm(e,p)==e['N'];checks+=1
        ep=poly_eval(packet,vals,p)
        assert len(ep['N'])-1==929 and len(ep['polynomial'])-1==938
        actual_rays.append({'prime':p,'norm_degree':929,'product_degree':938})
    live={packet['output']}
    for n,op,x,y in reversed(packet['source']):
        assert n in live,('unused gate',n)
        live.update(v for v in [x,y] if isinstance(v,str))
    assert set(VARIABLES+PORTS)<=live
    receipt={'independent_formal_radical_products':checks,'degree_rays':rays,'actual_coefficient_degree_rays':actual_rays,'whole_tuple_payloads_verified':bound_files,'all_gates_and_ports_live':True,'delivered_circuits_regenerated_exactly':True,'product_operations':122,'system_operations':117,'scope':'Finite diagnostics; the mathematical proof supplies the universal identity, exact degree, and compiler equivalence.'}
    Path(__file__).with_name('CHECK_RESULTS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
