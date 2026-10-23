#!/usr/bin/env python3
"""Independent-formula modular replay and source certificate; not a kernel proof."""
from pathlib import Path
from collections import Counter
import hashlib, importlib.util, json, random, subprocess, sys
from check_jones import auth, fixed, literal, algebra_tests, coprime_crt_tests, require
R=Path(__file__).resolve().parent
NAME='signed_coprime_compact_split_crt'
def main():
    body=json.loads((R/'generated'/f'{NAME}.json').read_text());ports,payloads=auth()
    for item in json.loads((R/'SOURCE_PINS.json').read_text())['files']:
        require(hashlib.sha256((R/item['local_path']).read_bytes()).hexdigest()==item['sha256'],'source pin '+item['local_path'])
    binding=json.loads((R/'FIXED_BINDING.json').read_text())
    require(binding['additional_fixed_leaves']['threshold_scale']=={'value':'2^18146981','exponent':18146981},'active fixed threshold')
    spec=importlib.util.spec_from_file_location('independent_source',R/'split/verify_split.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);source=mod.audit()
    require(body['operations']==519 and body['exact_degree']==10461744,'expected metric')
    require(body['positivity_pad_exponent']==1946 and body['W']==108 and body['Kh']==1954 and body['E']==2064,'source dimensions')
    require(body['threshold_scale_exponent']==18146981 and body['threshold_B_power']==1089 and body['threshold_epsilon_power']==3,'threshold parameters')
    counts=Counter(n['kind'] for n in body['nodes'] if n['kind'] in ('add','sub','mul'));require(dict(counts)==body['operation_counts'],'gate counts')
    require(len(body['variables'])==13 and len(set(body['variables']))==13,'unknown count')
    rng=random.Random(913108);trials=0;cert=[]
    for prime in (101,1009,1000003):
        fv=fixed(body,ports,prime)
        for _ in range(90):
            vv={n:rng.randrange(-5,6) for n in body['variables']};out=[]
            for k,n in enumerate(body['nodes']):
                kind=n['kind']
                if kind=='variable':x=vv[n['name']]
                elif kind=='literal':x=n['value']
                elif kind=='fixed':x=fv[n['name']]
                else:
                    require(n['left']<k and n['right']<k,'topology');a,b=out[n['left']],out[n['right']];x=a+b if kind=='add' else a-b if kind=='sub' else a*b
                out.append(x%prime)
            wanted,regs=literal(body,vv,ports,prime,{})
            require(out[body['output']]==wanted,'independent full formula')
            for n,k in body['named_nodes'].items():require(out[k]==regs[n],'named formula '+n)
            trials+=1
        deg=[];lead=[]
        for n in body['nodes']:
            kind=n['kind']
            if kind=='variable':d,c=1,1
            elif kind=='literal':d,c=0,n['value']%prime
            elif kind=='fixed':d,c=0,fv[n['name']]
            else:
                a,b=n['left'],n['right']
                if kind=='mul':d,c=deg[a]+deg[b],lead[a]*lead[b]%prime
                else:d=max(deg[a],deg[b]);c=((lead[a] if deg[a]==d else 0)+(1 if kind=='add' else -1)*(lead[b] if deg[b]==d else 0))%prime
            deg.append(d);lead.append(c)
        require(deg[body['output']]==10461744 and lead[body['output']]!=0,'exact degree')
        cert.append({'prime':prime,'leading_residue':lead[body['output']]})
    for k in range(1,101,2):
        nu=2134940+2*k
        require(2195*nu-31*k-21==2*(18146981+1089*nu)+3*(k-1),'odd-base square threshold')
    result={'status':'PASS','variables':13,'operations':519,'degree':10461744,'independent_modular_replays':trials,'exact_degree_certificates':cert,'source':source,'algebra':algebra_tests(),'coprime_crt':coprime_crt_tests(),'payloads':payloads,'scope':'Finite implementation checks; imported mathematical compiler/Jones theorems are not re-proved by this script.'}
    (R/'generated/CHECKS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
