#!/usr/bin/env python3
import hashlib,itertools,json,os,sys,time
from pathlib import Path
from collections import Counter
OUT=Path(__file__).resolve().parent
BASE=Path(sys.argv[1]) if len(sys.argv)>1 else OUT.parent/'pa195_conpa/pa195'
os.environ['PA195_REFERENCE']=str(BASE)
import router_fast_snapshot as r
from exact_router_support import install
install(r)
from cpp_router_filter import install as install_cpp_filter
install_cpp_filter(r)
P=r.P;v=r.v;c=r.c
symbols=json.loads((OUT/'input/symbols.json').read_text());symbols=[tuple(x) if isinstance(x,list) else x for x in symbols]
seed_receipt=json.loads((OUT/'input/seeds.json').read_text())
inputs={name:(OUT/'input'/name).read_text().splitlines() for name in {z['source'] for z in seed_receipt['checks']}}
start=time.time();checks=[];hist=Counter();successes=[]

def writegrammar(t,path):
    nodes={};rules={}
    def visit(x):
        if not c.isnode(x):return list(x) if isinstance(x,tuple) else x
        if x in nodes:return nodes[x]
        name='g'+str(len(nodes));nodes[x]=name
        rules[name]=[visit(x[0]),visit(x[1])];return name
    root=visit(t);path.write_text(json.dumps({'root':root,'rules':rules},indent=2)+'\n')

def startup(rows):
    physical=[0,0,0,0,0,0,2,0,0]+[1]*26
    want={-3,-2,46};pos=47
    for value in physical:pos+=1;want.update(range(pos,pos+value+1));pos+=value+1
    q,head,ones=74,0,set()
    for tick in range(58154*64+1):
        if q==84 and head==-2 and ones==want:return {'steps':tick,'native_state':84,'head':-2,'exact_complete_tape':True}
        if q==254:raise ValueError('startup halted')
        w,d,q=rows[q,int(head in ones)];(ones.add if w else ones.discard)(head);head+=1 if d else-1
    raise ValueError('startup exceeded bound')

for i,seed in enumerate(seed_receipt['checks']):
    doc=json.loads(inputs[seed['source']][seed['line']]);tt=[]
    def at(x):return symbols[-1-x] if x<0 else tt[x]
    for a,b in doc['rules']:tt.append((at(a),at(b)))
    t=tt[doc['root']];raw,ix,shape=c.build(t)
    rec={'seed_file':seed['source'],'seed_line':seed['line'],'raw_states':len(raw)//2,'readers':len(shape),'modes':{}}
    for base_mode,sh in [('AX',shape),('all_controls',{q:None for q,_ in raw if q!=74})]:
      for helper_count in (1,2):
        mode=base_mode+':helpers'+str(helper_count)
        one=(r.one_router_candidates if helper_count==1 else r.two_router_candidates)(raw,sh,194)
        mr={k:value for k,value in one.items() if k!='hits'};mr['optimistic_hits']=len(one['hits']);mr['exact_attempts']=0;mr['compatible_hits']=0
        hist[mode+':'+str(one['best_optimistic'])]+=1
        concrete=([(router,) for router,upper in one['hits']] if helper_count==1 else [routers for ra,rb,upper in one['hits'] for routers in itertools.product(ra,rb)])
        for routers in concrete:
            mr['exact_attempts']+=1
            ans=r.exact_folds(raw,sh,list(routers),one['target_folds'])
            if ans is None:continue
            folded,fs,cert,rr=ans;mr['compatible_hits']+=1
            name='candidate'+str(len(folded)//2)+'_'+str(i)+'_'+mode.replace(':','_')+'_'+str(mr['exact_attempts']);D=OUT/name;D.mkdir(exist_ok=True)
            writegrammar(t,D/'grammar.json')
            labels=[74]+sorted({q for q,_ in folded}-{74})+[254];inv={q:j for j,q in enumerate(labels)}
            dense={(inv[q],b):(w,d,inv[n]) for(q,b),(w,d,n)in folded.items()}
            for filename,table in [('parent.native.tm',raw),('parent_with_router.native.tm',rr),('candidate.native.tm',folded),('candidate.tm',dense)]: (D/filename).write_bytes(v.table_bytes(table))
            for filename,value in [('folds.json',fs),('local_certificate.json',cert),('labels.json',labels),('routers.json',routers)]: (D/filename).write_text(json.dumps(value,indent=2)+'\n')
            sites,cfg,cs=c.source(t);source=v.source_binding(t,sites,cfg);emitter=v.emitter(t)
            unchanged=all(folded[q,b]==raw[q,b] for q in c.BOXSTATES for b in (0,1))
            runtime={'parent':c.validate(raw,cs)}
            if unchanged:runtime['folded']=c.validate(folded,cs)
            initial=startup(folded)
            result={'source':source,'emitter':emitter,'runtime':runtime,'protected_engine_unchanged':unchanged,'startup':initial,'working_states':len(folded)//2,'dense_sha256':hashlib.sha256(v.table_bytes(dense)).hexdigest(),'folds':len(fs),'local_cases':cert['local_cases']}
            (D/'validation.json').write_text(json.dumps(result,indent=2)+'\n')
            successes.append(str(D));print('CANDIDATE',str(D),json.dumps(result),flush=True)
        rec['modes'][mode]=mr
    checks.append(rec)
    print('GRAMMAR',i+1,'of',len(seed_receipt['checks']),'best',[(m,z['best_optimistic'],z['optimistic_hits'],z['compatible_hits']) for m,z in rec['modes'].items()],'seconds',round(time.time()-start,2),flush=True)
receipt={'grammars':len(checks),'input_files_sha256':{name:hashlib.sha256((OUT/'input'/name).read_bytes()).hexdigest() for name in inputs},'router_filter_cpp_sha256':hashlib.sha256((OUT/'router_filter.cpp').read_bytes()).hexdigest(),'router_api_sha256':hashlib.sha256((OUT/'router_fast_snapshot.py').read_bytes()).hexdigest(),'best_optimistic_histogram':dict(hist),'successes':successes,'checks':checks,'seconds':time.time()-start,'exact_cycle_detection':True,'strict_all_incoming_histories':True,'scope':'One or two additional read-only history router with existing child controls; opposite-history two-cell contextual folds; AX-only and all old controls except start. Matching is a filter and all optimistic improving candidates receive exact simultaneous local checking.'}
(OUT/'cpp_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('DONE',json.dumps({k:v for k,v in receipt.items() if k!='checks'}),flush=True)
