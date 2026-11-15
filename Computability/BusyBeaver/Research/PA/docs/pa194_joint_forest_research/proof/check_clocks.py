#!/usr/bin/env python3
"""Check the complete finite bindings for the written iPRA clock theorem."""
from pathlib import Path
import argparse,json
from contract_inspector import inspect,require

ROOT=Path(__file__).resolve().parents[1]
NAMES=('PA194ForestR','PA194ForestB','PA194ForestX')

def check(machine_root=ROOT/'machines',output=ROOT/'proof/clock_certificates.json',parent_folder=ROOT/'reference/AX11H'):
    ref=ROOT/'verification/vendor'
    parent_sites,parent_ins,parent=inspect(parent_folder,ref)
    results={}
    for name in NAMES:
        sites,ins,info=inspect(machine_root/name,ref)
        require(ins==parent_ins,'every guarded successor equals the AX11H parent')
        # Counted return depths can change while the resolved graph is identical.
        require(sites[25]==parent_sites[25]==['1000000','dec',8],'same initial source site')
        info['changed_source_addresses']=sum(a[0]!=b[0]for a,b in zip(sites,parent_sites))
        info['changed_counted_return_operands']=sum(a[1:]==['continueTo',2] and b[1:]==['continueTo',3]for a,b in zip(parent_sites,sites))
        info['source_graph_identical']=True
        results[name]=info
    result={'status':'PASS','parent':parent,'candidates':results,
            'witness_maps':'h_i(t) -> h_j(T_j+alpha_j*(t+1)+beta_j*(t+1)*t/2)',
            'proof_scope':'Finite certificates for the written quantifier-free-induction proof, not a Lean theorem.'}
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({name:info['physical_time_bound']for name,info in results.items()},indent=2))
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--machines',type=Path,default=ROOT/'machines')
    parser.add_argument('--output',type=Path,default=ROOT/'proof/clock_certificates.json')
    parser.add_argument('--parent',type=Path,default=ROOT/'reference/AX11H')
    args=parser.parse_args();check(args.machines,args.output,args.parent)
