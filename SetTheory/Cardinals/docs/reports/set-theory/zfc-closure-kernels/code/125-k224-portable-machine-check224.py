#!/usr/bin/env python3
"""Independent finite whole-tape proof and complete blank startup for Rel224.

No builder, search tool, fold prover, or symbolic runtime engine is imported.
The local theorem quantifies over every binary initial tape and every initial
head position. Source/theory calibration and universal runtime are separate.
"""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parent
OLD_SHA='4526bd8cf2160ac5dfce039add0550e9788095f60ecc6b4462afd4ebbfd42790'
K_SHA='f886dd8d11e9705c5315140f68d5ae2f26c80afb015e08074c7e3da1414fa37f'
CANON_SHA='6361b0b29c2e0485bf8cf025dcf2606c2fac071f3f6e24fbde04016466d92168'
SOURCE_SHA='309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878'

def need(condition,message):
    if not condition:raise ValueError(message)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def digest(value):return hashlib.sha256((json.dumps(value,separators=(',',':'))+'\n').encode()).hexdigest()
def parse(path):
    rows={};starts=[]
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):starts.append(int(line[9:]))
        if not line or line.startswith('#'):continue
        q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
        need((q,b)not in rows and b in(0,1)and w in(0,1)and d in('L','R'),'Malformed row')
        rows[q,b]=(w,1 if d=='R'else-1,z)
    states={q for q,b in rows};terminals={z for w,d,z in rows.values()}-states
    need(len(starts)==1 and starts[0]in states,'Invalid initial state')
    need(set(rows)=={(q,b)for q in states for b in(0,1)}and len(terminals)==1,'Incomplete/nonbinary table')
    return rows,starts[0],next(iter(terminals)),states

def fold(old,new):
    need(len(old)==450 and len(new)==448,'Wrong fold state census')
    phi=lambda q:157 if q==191 else q
    expected={(q,b):(w,d,phi(z))for(q,b),(w,d,z)in old.items()if q!=191}
    expected[157,0]=(0,-1,67);expected[157,1]=(1,-1,148)
    need(new==expected,'The supplied candidate differs from the fixed fold')
    # Every occurrence of either state has an immediate incoming transition.
    # The initial state is0. Each listed incoming row writes its tag then
    # moves right, proving the left-cell fact without an abstraction heuristic.
    incoming={157:[],191:[]}
    for(q,b),(w,d,z)in sorted(old.items()):
        if z in incoming:
            need(d==1 and w==(0 if z==157 else 1),'Incoming row violates predecessor tag')
            incoming[z].append([q,b,w,d,z])
    need(all(incoming.values()),'A folded state has no incoming row')
    old_rows={(157,0):(0,1,90),(157,1):(1,1,86),(191,0):(0,1,155),(191,1):(1,1,182)}
    need(all(old[k]==v for k,v in old_rows.items()),'Unexpected exceptional old row')
    proofs=[]
    for q,tag in((157,0),(191,1)):
        for b in(0,1):
            initial={-1:tag,0:b};cells=dict(initial);s=157;h=0;trace=[]
            steps=5 if(q,b)==(191,0)else 3
            w,d,z=old[q,b];target=dict(initial);target[0]=w
            for i in range(steps):
                need(s!=254,'Interior halt')
                need(h in cells,'Block reads arbitrary exterior')
                read=cells[h];ww,dd,zz=new[s,read];trace.append([s,h,read,ww,dd,zz])
                cells[h]=ww;h+=dd;s=zz
            need((s,h,cells)==(phi(z),d,target),'Exceptional block does not preserve the entire tape and mapped endpoint')
            proofs.append(dict(old_state=q,read=b,predecessor_tag=tag,old_steps=1,new_steps=steps,
                initial_cells=initial,trace=trace,final_cells=cells,endpoint=[s,h],
                arbitrary_exterior_untouched=True,no_interior_halt=True))
    ordinary=0
    for(q,b),(w,d,z)in old.items():
        if q in(157,191):continue
        need(new[q,b]==(w,d,phi(z)),'Ordinary row does not commute');ordinary+=1
    need(ordinary==446,'Wrong ordinary-row count')
    return dict(status='INDEPENDENT_ALL_TAPE_225_TO_224_FOLD_PASS',state_map={'191':157,'others':'identity'},
        predecessor_facts={'157':{'-1':0},'191':{'-1':1}},incoming_rows=incoming,
        ordinary_one_step_rows=ordinary,exceptional_blocks=proofs,positive_block_histogram={'1':446,'3':3,'5':1},
        scope='Every binary initial tape, common initial state0, and every integer initial head. Each old step matches a positive new block. Nonhalting endpoints have exactly the mapped state, head and whole tape; there are no interior halts.')

def execute(rows,start,halt,ticks):
    state=start;head=0;ones=set();used=Counter()
    for _ in range(ticks):
        need(state!=halt,'Unexpected early halt in bootstrap')
        b=int(head in ones);used[state,b]+=1;w,d,state=rows[state,b]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=d
    return state,head,ones,used

def expected_frame():
    logical=[3,0,0,0,3,0,0,0,0];physical=[None]*9
    for logical_index,physical_index in enumerate([6,2,0,4,3,7,8,5,1]):physical[physical_index]=logical[logical_index]
    ones={-6,176};cursor=177
    for value in physical+[1]*167:
        cursor+=1;ones.update(range(cursor,cursor+value+1));cursor+=value+1
    return ones,logical,physical

def startup(old,new,canonical,mapping):
    ones,logical,physical=expected_frame();old_ticks=409835
    q,h,tape,used=execute(old,0,254,old_ticks)
    need((q,h,tape)==(84,-5,ones),'Rel225 does not reach the expected complete blank frame')
    extra=2*(used[157,0]+used[157,1]+used[191,1])+4*used[191,0]
    ticks=old_ticks+extra
    nq,nh,ntape,nused=execute(new,0,254,ticks)
    need((nq,nh,ntape)==(84,-5,ones),'Rel224 does not reach the expected complete blank frame')
    cq,ch,ctape,cused=execute(canonical,0,224,ticks)
    need((cq,ch,ctape)==(mapping[84],-5,ones),'Canonical224 blank frame differs')
    return dict(status='EXACT_COMPLETE_BLANK_STARTUP_PASS',old_steps=old_ticks,new_steps=ticks,additional_steps=extra,
        old_exceptional_row_visits={f'{q}/{b}':used[q,b]for q in(157,191)for b in(0,1)},
        dispatcher_k=84,dispatcher_canonical=mapping[84],head=-5,one_cells=sorted(ones),all_other_cells=0,
        logical_registers=logical,physical_registers=physical,extra_gap=117,spares=[1]*167,
        rows_used=len(nused),canonical_rows_used=len(cused))

def source_graph(path):
    sites=json.loads(path.read_text());leaves={};prefixes=set()
    for i,row in enumerate(sites):
        need(isinstance(row,list)and len(row)==3,'Malformed source row')
        pc,op,arg=row
        need(isinstance(pc,str)and pc and set(pc)<={'0','1'}and pc not in leaves,'Malformed/duplicate prefix')
        need(op in('CI','CD','CB','CC','CH'),'Unknown source instruction')
        if op in('CI','CD'):need(type(arg)is int and 0<=arg<9,'Invalid register')
        elif op in('CB','CC'):need(type(arg)is int and arg>=1,'Invalid control argument')
        else:need(arg is None,'Invalid halt argument')
        leaves[pc]=i;prefixes.update(pc[:k]for k in range(len(pc)))
    need(sites==sorted(sites),'Source is not in leaf order')
    need(not(set(leaves)&prefixes)and all(p+b in leaves or p+b in prefixes for p in prefixes for b in'01'),'Source is not a complete prefix tree')
    depth=max(map(len,leaves));need(depth<=64,'Frame is too short for source')
    def resolve(bits):
        p='';k=0
        while p not in leaves:
            p+=bits[k]if k<len(bits)else'0';k+=1;need(k<=depth,'Cannot resolve source address')
        need('1'not in bits[k:],'Source successor leaves nonzero unread suffix')
        return leaves[p]
    def inc(bits):return format((int(bits,2)+1)%(1<<len(bits)),f'0{len(bits)}b')if bits else''
    def strip(bits,symbol,n):
        for i in range(len(bits)-1,-1,-1):
            if bits[i]==symbol:
                n-=1
                if n==0:return bits[:i]
        return''
    graph=[]
    for pc,op,arg in sites:
        if op=='CH':successors=[]
        elif op=='CI':successors=[resolve(inc(pc))]
        elif op=='CD':successors=[resolve(inc(pc)),resolve(inc(strip(pc,'0',1)))]
        elif op=='CB':successors=[resolve(inc(strip(pc,'0',arg)))]
        else:successors=[resolve(strip(pc,'1',arg))]
        graph.append([op,arg,successors])
    entry=resolve('');need(entry==0 and set(sites[entry][0])=={'0'},'Initial blank source address differs')
    metrics=dict(leaves=len(sites),guarded_cases=sum(2 if s[1]=='CD'else 1 for s in sites),maximum_depth=depth,
        maximum_zero_run=max(len(z)for pc in leaves for z in pc.split('1')),no_stray_successors=True,initial_leaf=sites[entry][0],graph_sha256=digest(graph))
    return sites,graph,metrics

def check(results,output):
    oldpath=ROOT/'reference/rel225.k.tm';kpath=results/'candidate224.k.tm';cpath=results/'candidate224.tm';lpath=results/'candidate224.legacy.tm';spath=results/'sites.json'
    need(sha(oldpath)==OLD_SHA and sha(kpath)==K_SHA and sha(cpath)==CANON_SHA and sha(spath)==SOURCE_SHA,'Pinned input or output hash mismatch')
    old,os,oh,ostates=parse(oldpath);new,ns,nh,nstates=parse(kpath);canonical,cs,ch,cstates=parse(cpath);legacy,ls,lh,lstates=parse(lpath)
    need((os,oh,ns,nh,cs,ch,ls,lh)==(0,254,0,254,0,224,95,254),'Unexpected initial or halting label')
    need(len(ostates)==225 and len(nstates)==224 and cstates==set(range(224)),'Wrong state count')
    proof=fold(old,new)
    renumber=json.loads((results/'renumbering224.json').read_text());mapping={int(q):z for q,z in renumber['k_to_canonical'].items()};klegacy={int(q):z for q,z in renumber['k_to_legacy'].items()}
    need(set(mapping)==nstates|{254}and set(mapping.values())==set(range(225))and len(mapping)==225,'Canonical map is not a bijection')
    need(mapping[0]==0 and mapping[254]==224,'Canonical initial/halt labels differ')
    need(canonical=={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in new.items()},'Canonical rows differ')
    need(set(klegacy)==set(mapping)and len(set(klegacy.values()))==225 and klegacy[0]==95 and klegacy[254]==254,'Legacy map is not a bijection')
    need(legacy=={(klegacy[q],b):(w,d,klegacy[z])for(q,b),(w,d,z)in new.items()},'Runtime proof table differs')
    order=[0];seen={0}
    for q in order:
        for b in(0,1):
            z=canonical[q,b][2]
            if z!=224 and z not in seen:seen.add(z);order.append(z)
    need(order==list(range(224)),'Canonical table is not the specified breadth-first numbering')
    sites,graph,metrics=source_graph(spath)
    need(spath.read_bytes()==(ROOT/'reference/sites.json').read_bytes(),'Fold changed the source')
    boot=startup(old,new,canonical,mapping)
    controls=[]
    for name in('wrong_predecessor_tag','broken_shared_helper','wrong_retained_row'):
        badold=dict(old);badnew=dict(new)
        if name=='wrong_predecessor_tag':badold[135,1]=(0,1,191);badnew[135,1]=(0,1,157)
        elif name=='broken_shared_helper':badold[67,1]=(0,1,152);badnew[67,1]=(0,1,152)
        else:badnew[157,0]=(0,-1,148)
        try:fold(badold,badnew)
        except ValueError as error:controls.append(dict(name=name,rejected=True,reason=str(error)))
        else:raise ValueError('Tamper control accepted: '+name)
    answer=dict(status='INDEPENDENT_224_FOLD_SOURCE_FRAME_AND_CANONICALIZATION_PASS',working_states=224,rows=448,
        input_table_sha256=sha(oldpath),k_table_sha256=sha(kpath),canonical_table_sha256=sha(cpath),legacy_table_sha256=sha(lpath),source_sha256=sha(spath),
        checker_sha256=sha(Path(__file__)),fold=proof,source_metrics=metrics,blank_startup=boot,negative_controls=controls,
        label_isomorphisms_checked=True,source_preserved=True,
        proof_status='Ordinary finite mathematical verification; no new proof-assistant kernel endpoint.',
        scope='The exact225-to224 whole-tape simulation, complete blank bootstrap, source successor closure and table isomorphisms are checked here. Upstream source/theory calibration and the full universal binary runtime remain separately reported obligations.')
    output.parent.mkdir(parents=True,exist_ok=True);output.write_text(json.dumps(answer,indent=2)+'\n');return answer
if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--results',type=Path,default=ROOT/'results');ap.add_argument('--output',type=Path);a=ap.parse_args()
    result=check(a.results,a.output or a.results/'independent224.json')
    print(json.dumps({k:v for k,v in result.items()if k not in('fold','blank_startup')},indent=2))
    print('Four exact whole-tape blocks:3,3,5,3; complete blank startup:',result['blank_startup']['new_steps'])
