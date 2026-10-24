#!/usr/bin/env python3
"""Serialize proposed sign implications and literal raw compiler interfaces."""
from pathlib import Path
import json,sys
from hashlib import sha256
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
from build_projected import construct
import sign_rule_producer as S

def write(path,data):path.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')
def cook(i):
    r=S.RULES[i]
    return {'row':r['row'],'target':list(r['target']),'sign':r.get('sign',1)}

def main():
    root=HERE.parent
    seeds=json.loads((root/'domain_guard_seeds.json').read_text())['guards']
    known,hist=S.closure(seeds,True)
    source=json.loads((root/'provenance/upstream/wire_eliminated_source.json').read_text())
    b,_,_=construct(source)
    names={v['name']:i for i,v in enumerate(b.variables)}
    finalnames={v['name']:i for i,v in enumerate(S.EQ['variables'])}
    rawpowers=[]
    for i,((n,k),m) in enumerate(b.powers.items()):
        X,Y=b.shared_indices[k];T=b.shared_bases[n]
        rawpowers.append({'base':list(n),'exponent':list(k),'output':list(m),
                          'X':list(X),'Y':list(Y),'T':list(T),
                          'quotient':['v',names[f'pow{i}.quotient']],
                          'row':next(j for j,r in enumerate(b.rows) if r['label']==f'pow{i}.power_congruence')})
    frame={}
    for name,atom in zip(('W','A','Z'),b.shared_parameters):frame[name]=list(atom)
    frame['norm_row']=next(j for j,r in enumerate(b.rows) if r['label']=='shared.last_norm')
    frame['sum_row']=next(j for j,r in enumerate(b.rows) if r['label']=='shared.frame_definition')
    frame['bases']=[{'base':list(n),'T':list(T),
                     'row':next(j for j,r in enumerate(b.rows) if r['label']==f'base{i}.T_definition')}
                    for i,(n,T) in enumerate(b.shared_bases.items())]
    extras=[]
    for atom in b.shared_bases.values():
        i=finalnames[b.variables[atom[1]]['name']]
        extras.append([i,1]);known.update({(i,0),(i,1)})
    for X,Y in b.shared_indices.values():
        i=finalnames[b.variables[X[1]]['name']]
        extras.append([i,0]);known.add((i,0))
    post=[];changed=True
    while changed:
        changed=False
        for i,r in enumerate(S.RULES):
            if r['target'] not in known and r['requires']<=known:
                known.add(r['target']);post.append(i);changed=True
    if not all((i,0) in known for i in range(S.N)):raise ValueError('domain not restored')
    cert={'schema':'pell_frame_domain_recovery_v1','guards':seeds,
          'pre_steps':[cook(i) for i in hist],'frame_conclusions':extras,
          'post_steps':[cook(i) for i in post],'final_nonnegative_count':S.N,
          'final_equation_sha256':sha256((root/'equations_v3/cap64/equation.json').read_bytes()).hexdigest()}
    raw={'schema':'raw_compiler_frame_interface_v1','variables':b.variables,'rows':b.rows,
         'gates':[{'op':op,'left':list(a),'right':list(c),'out':list(out)} for (op,a,c),out in b.cache.items()],
         'frame':frame,'powers':rawpowers}
    write(root/'DOMAIN_CERTIFICATE.json',cert);write(root/'RAW_FRAME_INTERFACE.json',raw)
    print(json.dumps({'guards':len(seeds),'pre_steps':len(hist),'frame_facts':len(extras),
                      'post_steps':len(post),'all_nonnegative':S.N},indent=2))
if __name__=='__main__':main()
