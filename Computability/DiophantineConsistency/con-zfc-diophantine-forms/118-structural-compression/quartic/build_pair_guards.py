#!/usr/bin/env python3
"""Make six quadratic pair guards before all source interpretations."""
from pathlib import Path
import json,sys,copy,hashlib
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'upstream'))
import terminal_elimination as engine

PAIRS=[(585,586,574,576,577),(593,594,574,576,577),
       (601,602,574,576,577),(619,620,608,610,611),
       (637,638,626,628,629),(562,563,547,549,550)]

def read(name):return json.loads((HERE/name).read_text())
def write(path,data):
    p=HERE/path;p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')

def normalize_projection_metadata(output,certificate):
    """Bind the generated equation to this packet's actual certificate name."""
    output['elimination']['certificate']='projection.json'
    certificate['output_sha256']=hashlib.sha256(engine.canonical_bytes(output)).hexdigest()

def make_parent(old,domain):
    n,nr=domain['baseline_body_variables'],domain['baseline_body_rows']
    mp={raw:j for j,raw in enumerate(domain['baseline_raw_indices'])}
    removed={i for pair in PAIRS for i in pair[:2]}
    keep=[g['predicate']for g in domain['guards'] if not(g['predicate']['kind']=='retained_scalar'and g['predicate']['raw_variables'][0]in removed)]
    if len(keep)!=63:raise ValueError('expected 63 unchanged predicates')
    preds=copy.deepcopy(keep)+[dict(kind='shared_modulus_pair',raw_variables=[r,s],terms=[[1,[mp[r],mp[s]]]])for r,s,*_ in PAIRS]
    new=dict(schema='quadratic_sum_squares_v1',domain='unrestricted integers',variant='shared_modulus_pair69_raw',variables=copy.deepcopy(old['variables'][:n]),residuals=copy.deepcopy(old['residuals'][:nr]))
    guards=[]
    for j,p in enumerate(preds):
        a,b,c=range(len(new['variables']),len(new['variables'])+3)
        new['variables'].extend(dict(kind='nonnegative_guard',name=f'pair69_guard.{j}.{s}')for s in ['a','b','c'])
        new['residuals'].append(dict(label=f'pair69_guard.{j}',terms=p['terms']+[[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]))
        guards.append(dict(predicate=p,auxiliary=[a,b,c]))
    if len(guards)!=69:raise ValueError('69 predicates')
    return new,dict(baseline_body_variables=n,baseline_body_rows=nr,baseline_raw_indices=domain['baseline_raw_indices'],guards=guards,removed_scalar_indices=sorted(removed),pair_recovery=PAIRS)

def main():
    old=read('factorial-radius-output-sign-profile_raw_parent.json')
    domain=read('factorial-radius-output-sign-profile_raw_domain.json')
    new,newdomain=make_parent(old,domain)
    write('pair69/parent.json',new)
    write('pair69/domain.json',newdomain)
    census={}
    for family,eq in [('old75',old),('pair69',new)]:
        for cap in [8,16,32]:
            out,cert,metrics=engine.optimize(eq,max_support=cap)
            normalize_projection_metadata(out,cert)
            engine.verify(eq,out,cert)
            if cert['unconstrained_removed']:raise ValueError('unconstrained deletion')
            name=f'{family}/support{cap}'
            write(name+'/equation.json',out);write(name+'/projection.json',cert);write(name+'/polynomial.json',engine.expand(out))
            census[name]=metrics
            print(name,metrics,flush=True)
    write('CENSUS.json',census)

if __name__=='__main__':main()
