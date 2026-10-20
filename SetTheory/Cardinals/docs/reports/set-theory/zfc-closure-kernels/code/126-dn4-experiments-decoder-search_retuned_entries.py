#!/usr/bin/env python3
"""Search literal one-row entries for newly required CB2/CC4 instructions.

The first pass is only a symbolic target-contract screen using the inherited
block summaries. Survivors reprove those summaries and representative cases.
Complete source/runtime and blank startup replay remain a separate gate.
"""
from retune_rotations import *
sys.path.insert(0,str(P/'baseline226/vendor/proveit'));import symbolic_runtime as engine
import inspect
namespace=engine.__dict__.copy()
exec(inspect.getsource(engine.case).replace('range(4000)','range(512)'),namespace)
discovery_case=namespace['case']

path=Path(__file__).parent/'full_dn4';t,_=v.parse_table((path/'simplified.tm').read_bytes())
lr=labeled(t,c.tree(json.loads((path/'sites225.json').read_text())));graph,_=c.graph_arithmetic(c.sites(unlabel(lr)))
out=Path(__file__).parent/'retuned_entry_search';out.mkdir(exist_ok=True)
mp={int(k):z for k,z in json.loads((path/'state_map.json').read_text()).items()};mp[233]=533;mp[254]=254
mapping=lambda x:{(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in x.items()}
old=mapping(t);lemmas,_=engine.prove_blocks(old);counts=collections.Counter();records=[]
for index,rot in enumerate(moves(t,lr,True)):
    tt,ur=perform(t,lr,rot);r,rec=repair(ur,graph)
    if r is None or len(rec.get('row_commands',{}))!=1:continue
    port,command=next(iter(rec['row_commands'].items()))
    if command not in(('CB',2),('CC',4)):continue
    sites=c.sites(unlabel(r));i=rec['changes'][0][0];site=sites[i];metrics=c.metrics(unlabel(r))
    print('SOURCE',index,rot,'port',port,command,'metrics',metrics,flush=True)
    old=mapping(tt);states=sorted({q for q,b in tt});hits=[]
    for w,d,z in itertools.product((0,1),(-1,1),states):
        counts['target_contract_trials']+=1;row=(w,d,z);new=old.copy();new[mp[port[0]],port[1]]=(w,d,mp[z])
        try:discovery_case(new,lemmas,site,False)
        except Exception:continue
        counts['target_contract_passes']+=1;uu=tt.copy();uu[port]=row
        try:
            llm,blocks=engine.prove_blocks(new);seen=set()
            for j,s in enumerate(sites):
                for pos in((False,True)if s[1]=='CD'else(False,)):
                    key=tuple(s[1:])+(pos,)
                    if key in seen:continue
                    seen.add(key);engine.case(new,llm,s,pos)
        except Exception as exc:
            counts['representative_failure']+=1;continue
        counts['representative_pass']+=1
        u,r2,f=probe_folds(uu,r);n=len(u)//2
        label=f'layout_{index}_{w}_{d}_{z}';label=('HIT_'if n<=224 else'')+label
        (out/(label+'.tm')).write_bytes(encode(u));c.dump(out/(label+'_sites.json'),c.sites(unlabel(r2)))
        receipt=dict(rotation=rot,row=list(port)+list(row),source_changes=rec['changes'],metrics=metrics,states=n,folds=f,representative_cases=len(seen))
        c.dump(out/(label+'_receipt.json'),receipt);hits.append(receipt)
        print('PASS',label,'states',n,'score',f['score'],'representative_cases',len(seen),flush=True)
    records.append(dict(rotation=rot,port=port,command=command,hits=hits))
c.dump(out/'summary.json',dict(target_symbolic_step_bound=512,counts=dict(counts),records=records));print('DONE',dict(counts),flush=True)
