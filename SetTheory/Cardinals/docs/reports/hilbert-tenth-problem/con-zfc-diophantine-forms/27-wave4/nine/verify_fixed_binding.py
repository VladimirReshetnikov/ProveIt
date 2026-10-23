#!/usr/bin/env python3
"""Authenticate a full fixed tuple and replay Jones index/endpoint residues.

This finite test binds all 348 leaves together. It neither certifies a new
compiler theorem nor decides whether the equation has a solution.
"""
from pathlib import Path
from hashlib import sha256
from math import isqrt
import argparse,json
import build_improved as imp
nc=imp.nc;ROOT=Path(__file__).resolve().parent

def value(records,values,mod):
    return sum(r['coefficient']*__import__('functools').reduce(lambda a,b:a*b%mod,
        (pow(v,e,mod) for v,e in zip(values,r['powers'])),1) for r in records)%mod

def run(directory):
    constants=json.loads((ROOT/'source/nine/generated/constants.json').read_text())
    bound=json.loads((ROOT/'source/nine/generated/index_bound_s.json').read_text())
    assert constants['fixed_port_order']==bound['fixed_port_order']==['beta','K0','MC','MF']
    paths={name:directory/'expanded'/file for name,file in [('beta','beta.bin'),('K0','K.bin'),('MC','MC.bin'),('MF','MF_source.bin')]}
    ports={name:int.from_bytes(p.read_bytes(),'little') for name,p in paths.items()}
    assert all(v>=0 for v in ports.values())
    keys=[(tuple(c['alpha']),c['name']) for c in constants['coefficient_records']]
    old={w:nc.make_body(32,keys,w) for w in ['literal','majorant']}
    new={w:imp.make_body(32,keys,w) for w in ['literal','majorant','natural-majorant']}
    specialized_keys,aliases=imp.canonical_coefficients(constants)
    new.update({w+'_specialized':imp.make_body(32,specialized_keys,w) for w in ['literal','majorant','natural-majorant']})
    records=[]
    for prime in [101,1009,1000003]:
        assert all(prime%j for j in range(2,isqrt(prime)+1))
        pvals=[ports[name]%prime for name in constants['fixed_port_order']]
        s=value(bound['terms'],[ports[name]%(prime-1) for name in constants['fixed_port_order']],prime-1)
        z=pow(2,s,prime)
        fixed={'z_index':z}
        coeffs={tuple(c['alpha']):value(c['coefficient_polynomial_in_fixed_ports'],pvals,prime) for c in constants['coefficient_records']}
        fixed.update({name:coeffs[a] for a,name in keys})
        B=2*z%prime;L=constants['L']
        y=sum((z+coeffs.get(a,0))*pow(B,L-nc.expo(a),prime) for a in nc.all_alphas(32))%prime
        d=nc.DAG();b=d.var('B');znode=d.fixed('z_index')
        e=imp.coding_blocks(d,b,32,keys,znode)[3]
        nodes,root,names=d.prune(e)
        fast,_=nc.evaluate_dag({'nodes':nodes,'output':root,'named_nodes':names},fixed,{'B':B},prime)
        assert y==fast
        fixed['y_index']=y
        samples=[]
        for a in [[0]*9,[1]*9,list(range(9)),[3,5,1,8,2,6,7,4,0]]:
            row={}
            for weight,body in new.items():
                got,_=nc.evaluate_dag(body,fixed,dict(zip(body['variables'],a)),prime)
                base_weight=weight.removesuffix('_specialized')
                if base_weight in old:
                    baseline,_=nc.evaluate_dag(old[base_weight],fixed,dict(zip(old[base_weight]['variables'],a)),prime)
                    assert got==baseline
                if weight.endswith('_specialized'):assert got==row[base_weight]
                row[weight]=got
            samples.append({'unknowns':a,'output_residues':row})
        records.append({'prime':prime,'s_mod_prime_minus_one':s,'z':z,'y':y,'samples':samples})
    receipt={'status':'pass','scope':'Whole tuple binding and exact modular implementation comparisons only; compiler semantics validated separately.',
             'port_order':constants['fixed_port_order'],'port_files':{name:{'file':p.name,'sha256':sha256(p.read_bytes()).hexdigest(),'bit_length':ports[name].bit_length()} for name,p in paths.items()},
             'weighted_coefficient_records':len(keys),'fixed_leaves':len(keys)+2,'direct_fast_y_checks':len(records),'old_new_output_comparisons':48,'specialized_generic_output_comparisons':36,'fingerprints':records}
    (ROOT/'generated/FIXED_BINDING_VALIDATION.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='fingerprints'},indent=2))
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--coefficient-directory',type=Path,default=ROOT.parent/'coefficients')
    run(ap.parse_args().coefficient_directory.resolve())
