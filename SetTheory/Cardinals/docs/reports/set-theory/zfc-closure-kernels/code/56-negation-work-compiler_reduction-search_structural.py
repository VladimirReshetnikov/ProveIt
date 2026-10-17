#!/usr/bin/env python3
"""Experiment with semantics-preserving source rotations on permutation252.

Emits ordinary two-symbol tables; strict affine checks keep the four original
register-box contracts explicit. A result is a candidate, not a new kernel proof.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from functools import lru_cache
import argparse, hashlib, importlib.util, json, math, os, random, sys, time
from pathlib import Path
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
SOURCE = Path(os.environ.get('PROVEIT_SOURCE', HERE.parents[1] / 'source/ProveIt')).resolve()
ZFC = SOURCE / 'Computability/BusyBeaver/Research/ZFC'
sys.path[:0] = [str(HERE/'source27'), str(ZFC)]
import rotate_search as rotate
import candidate252_independent_audit as audit
sys.modules['cost_search'] = SimpleNamespace()
_spec = importlib.util.spec_from_file_location('strict_structural', SOURCE / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py')
strict = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(strict)

OLD = json.loads((HERE/'source27/decoder_entries.json').read_text())
NODES = {int(k): tuple(map(tuple,v)) for k,v in OLD['nodes'].items()}
ROOT = OLD['root']
RAW = (ZFC/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes()
assert hashlib.sha256(RAW).hexdigest() == audit.EXPECTED_SHA
BASE = audit.read_table(RAW)
OLD_FP = {v:int(n) for n,v in OLD['fingerprints'].items()}
modal = lambda counts: int(max(counts,key=counts.get))
NODE_LABELS = {n:modal(OLD['state_entries'][str(n)]) for n in NODES}
LEAF_LABELS = {k:modal(c) for k,c in OLD['leaf_entries'].items()}
CONTROL = defaultdict(Counter)
for n, pair in NODES.items():
    for bit,e in enumerate(pair):
        if e[0] in 'BC':
            for label, count in OLD['state_entries'][str(n)].items():
                CONTROL[e,bit][BASE[int(label),bit]] += count
PURE = {q for q,b in BASE if b == 0 and BASE[q,0][:2] == (0,'R') and BASE[q,1][:2] == (1,'R')}
PROTECTED = {q for q,b in audit.BOX_PAIRS} | {t for q,b in audit.BOX_PAIRS for t in [BASE[q,b][2]]} | {64,96}

def fingerprints(nodes):
    @lru_cache(None)
    def fp(e):
        text = ('N('+fp(nodes[e[1]][0])+','+fp(nodes[e[1]][1])+')' if e[0]=='N' else ':'.join(map(str,e)))
        return hashlib.sha256(text.encode()).hexdigest()
    return {n:fp(('N',n)) for n in nodes}

def mutate(nodes,root,n,exp,origins):
    """Hash-cons, retaining optional old-node labels as allocation hints."""
    new, seen, org = {}, {}, defaultdict(set)
    def intern(a,b,source=None):
        pair=a,b
        if pair not in seen:
            seen[pair]=len(new);new[seen[pair]]=pair
        q=seen[pair]
        if source is not None:org[q].update(origins.get(source,()))
        return ('N',q)
    @lru_cache(None)
    def edge(e):
        if e[0]=='N':
            if e[1]==n:
                result=edge(exp)
                if result[0]=='N':org[result[1]].update(origins.get(e[1],()))
                return result
            a,b=nodes[e[1]]
            return intern(edge(a),edge(b),e[1])
        if e[0]=='T':return intern(edge(e[1]),edge(e[2]))
        return e
    r=edge(('N',root))[1]
    return new,r,dict(org)

def emit(nodes,root,origins,allocation='origin'):
    if allocation in ('identity','identity_greedy'):
        return emit_identity(nodes,root,origins,allocation)
    f=fingerprints(nodes)
    entries={n:(96 if n==root else NODE_LABELS[OLD_FP[f[n]]]) for n in nodes if n==root or f[n] in OLD_FP}
    used=set(entries.values())
    fresh=[n for n in nodes if n not in entries]
    retired=(set(NODE_LABELS.values())-used)&PURE-PROTECTED
    allocation_log=[];nextstate=255
    for n in fresh:
        choices=[NODE_LABELS[o] for o in origins.get(n,()) if NODE_LABELS[o] in retired]
        if allocation=='fresh':choices=[]
        if allocation=='greedy' and not choices:choices=sorted(retired)
        if choices:
            label=min(choices);retired.remove(label)
        else:
            label=nextstate;nextstate+=1
        entries[n]=label
        allocation_log.append([n,label,sorted(origins.get(n,()))])
    def trans(e,bit):
        if e[0]=='N':return bit,'R',entries[e[1]]
        if e[0]=='B' and e[1]==1:return 0,'L',7 if bit==0 else 33
        if e[0] in 'BC':return CONTROL[e,bit].most_common(1)[0][0]
        return bit,'R',LEAF_LABELS[':'.join(map(str,e))]
    table=BASE.copy()
    for n in nodes:
        if n==root or f[n] not in OLD_FP:
            for b,e in enumerate(nodes[n]):table[entries[n],b]=trans(e,b)
    assert all(table[k]==BASE[k] for k in audit.BOX_PAIRS)
    return table,dict(entries=entries,allocation=allocation_log,retired_unassigned=sorted(retired))

def emit_identity(nodes,root,origins,allocation='identity'):
    """Keep optimized ancestor rows when their immediate entry labels persist.

    Opaque original decoder entries may implement several syntactic nodes. All
    emitted candidates are screened by the full strict runtime contract suite.
    """
    fp=fingerprints(nodes);entries={};owners={};claimed=defaultdict(list)
    for n in nodes:
        if n==root:
            owners[n]=ROOT;entries[n]=96
        elif fp[n] in OLD_FP:
            owners[n]=OLD_FP[fp[n]];entries[n]=NODE_LABELS[owners[n]]
        if n in entries:claimed[entries[n]].append(n)
    fresh=[n for n in nodes if n not in entries]
    nextstate=255
    for n in fresh:
        opts=sorted(origins.get(n,()),key=lambda o:(NODE_LABELS[o] not in PURE,o))
        opts=[o for o in opts if NODE_LABELS[o] not in claimed and NODE_LABELS[o] not in PROTECTED]
        if opts:
            owners[n]=opts[0];entries[n]=NODE_LABELS[opts[0]];claimed[entries[n]].append(n)
    retired=(set(NODE_LABELS.values())-set(entries.values()))-PROTECTED
    if allocation!='identity_greedy':retired&=PURE
    for n in fresh:
        if n in entries:continue
        if retired:
            label=min(retired);retired.remove(label)
        else:label=nextstate;nextstate+=1
        entries[n]=label;claimed[label].append(n)
    origin_entries={old:entries[n] for n in nodes for old in origins.get(n,())}
    assigned=set(entries.values())
    aliases={NODE_LABELS[o]:label for o,label in origin_entries.items()
             if NODE_LABELS[o] not in assigned and NODE_LABELS[o] not in PROTECTED}
    def redirected(label):return aliases.get(label,label)
    table={(q,b):(w,d,redirected(t)) for(q,b),(w,d,t) in BASE.items()}
    def old_edge(e):
        return ('N',redirected(NODE_LABELS[e[1]])) if e[0]=='N' else e
    def new_edge(e):return ('N',entries[e[1]]) if e[0]=='N' else e
    def transition(e,bit):
        if e[0]=='N':return bit,'R',entries[e[1]]
        if e[0]=='B' and e[1]==1:return 0,'L',7 if bit==0 else 33
        if e[0] in 'BC':
            w,d,t=CONTROL[e,bit].most_common(1)[0][0]
            return w,d,redirected(t)
        return bit,'R',redirected(LEAF_LABELS[':'.join(map(str,e))])
    changed=[];preserved=[]
    for n in nodes:
        owner=owners.get(n)
        preserve=(owner is not None and tuple(map(old_edge,NODES[owner]))==tuple(map(new_edge,nodes[n])))
        if preserve:
            preserved.append(n);continue
        changed.append(n)
        for bit,e in enumerate(nodes[n]):table[entries[n],bit]=transition(e,bit)
    assert all(table[k]==BASE[k] for k in audit.BOX_PAIRS)
    return table,dict(entries=entries,owners=owners,aliases=aliases,changed=changed,preserved=preserved)

def sites(nodes,root):
    todo=[(('N',root),'')]
    while todo:
        e,p=todo.pop()
        if e[0]=='N':
            a,b=nodes[e[1]];todo.extend([(b,p+'1'),(a,p+'0')])
        else:yield p,e

class Tracking(dict):
    def __init__(self,*args):super().__init__(*args);self.used=set()
    def __getitem__(self,k):self.used.add((int(k[0]),k[1]));return super().__getitem__(k)

def cases(nodes,root):
    for p,e in sites(nodes,root):
        k=e[0];r=e[1] if len(e)>1 else None
        physical=audit.NEWPHYS[r] if k in 'ID' else r
        for zero in ((True,False) if k=='D' else (None,)):
            nxt=audit.successor(p,'C'+k,r,zero)
            effect=('inc',physical) if k=='I' else ('dec',physical) if k=='D' and not zero else None
            right=([('r',0,1,41),('b',1),('box',('plain',effect))] if nxt is None else
                   [('b',int(b)) for b in nxt]+[('r',0,1,40-len(nxt)),('b',1),('box',('plain',effect))])
            yield p,e,zero,physical,strict.canon([('b',1)],right)

def check(table,nodes,root):
    traced=Tracking({(str(q),b):(w,d,str(t)) for(q,b),(w,d,t) in table.items()})
    count=0
    for p,e,zero,physical,target in cases(nodes,root):
        try:strict.run(traced,p,(physical,zero) if e[0]=='D' else None,target,halt=e[0]=='H',fuel=1000)
        except (AssertionError,KeyError) as ex:
            return {'passed':False,'cases_passed':count,'failure':{'path':p,'operation':e,'zero':zero,'reason':str(ex)}},traced.used
        count+=1
    return {'passed':True,'cases_passed':count},traced.used

def boot(table,limit):
    q,h,ones=64,0,set();used=set()
    for steps in range(limit+1):
        if q==96 and ones and h-1 in ones and min(ones)==h-1:
            future=[p for p in ones if p>=h]
            if future and min(future)-h>=40:
                header=min(future);i=header+1;v=[]
                while i not in ones and i+1 in ones:
                    i+=1;x=0
                    while i in ones:x+=1;i+=1
                    v.append(x-1)
                if len(v)>=9 and not any(p>=i for p in ones) and v[:9]==[0]*9:
                    return {'outcome':'zero_root','steps':steps,'head':h,'gap':header-h,'primary':v[:9],'spares':v[9:],'ones':sorted(ones)},used
        if q==254:return {'outcome':'halt','steps':steps},used
        if steps==limit:break
        used.add((q,int(h in ones)))
        w,d,q=table[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
    return {'outcome':'fuel_limit','steps':limit},used

def prune(table,used):
    retained={q for q,b in used|audit.BOX_PAIRS}|{64,96}
    out={(q,b):(w,d,t if t in retained|{254} else 64) for (q,b),(w,d,t) in table.items() if q in retained}
    assert all(out[k]==table[k] for k in used|audit.BOX_PAIRS)
    return out

def evaluate(nodes,root,origins,allocation,limit=150000,full_boot=True):
    zm=rotate.zero_metrics(nodes,root)
    if zm[1]>7 or zm[2]>39:return dict(outcome='shape_bound',zero_metrics=zm)
    try:table,emission=emit(nodes,root,origins,allocation)
    except (KeyError,IndexError) as ex:return dict(outcome='emission_failure',reason=str(ex))
    runtime,used=check(table,nodes,root)
    result=dict(outcome='runtime_pass' if runtime['passed'] else 'runtime_fail',runtime=runtime,decoder_nodes=len(nodes),zero_metrics=zm,allocated_states=len(table)//2,runtime_states=len({q for q,b in used|audit.BOX_PAIRS}),emission=emission)
    if not runtime['passed'] or not full_boot:return result
    startup,bootused=boot(table,limit);result['boot']=startup
    if startup['outcome']=='zero_root':
        pruned=prune(table,used|bootused)
        result.update(outcome='passed',working_states=len(pruned)//2,table=pruned)
    else:result['outcome']='boot_'+startup['outcome']
    return result

def save_candidate(result,nodes,root,origins,name,out):
    table=result.pop('table',None)
    path=out/(name+'.json')
    path.write_text(json.dumps(dict(result=result,root=root,nodes=nodes,origins={q:sorted(v) for q,v in origins.items()}),indent=2)+'\n')
    if table is not None:
        (out/(name+'.tm')).write_bytes(audit.encode(table))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--mode',choices=['baseline','single','anneal'],default='baseline');ap.add_argument('--allocation',choices=['origin','greedy','fresh','identity','identity_greedy'],default='origin');ap.add_argument('--output',type=Path,default=HERE/'results');ap.add_argument('--boot-limit',type=int,default=150000);ap.add_argument('--iterations',type=int,default=20000);ap.add_argument('--seed',type=int,default=252)
    args=ap.parse_args();args.output.mkdir(exist_ok=True,parents=True)
    origins={q:{q} for q in NODES};begun=time.monotonic()
    initial=evaluate(NODES,ROOT,origins,args.allocation,args.boot_limit)
    assert initial['outcome']=='passed' and initial['working_states']==252,initial
    save_candidate(initial,NODES,ROOT,origins,'baseline',args.output)
    print('BASELINE 252 runtime8391 boot82552 PASS',flush=True)
    if args.mode=='baseline':return
    results=[];counts=Counter();best=252
    if args.mode=='single':
        for i,(n,e,kind) in enumerate(rotate.options(NODES)):
            nn,r,oo=mutate(NODES,ROOT,n,e,origins)
            rr=evaluate(nn,r,oo,args.allocation,args.boot_limit)
            if rr.get('working_states',999)<best:
                best=rr['working_states'];save_candidate(rr,nn,r,oo,f'best_{i}_{best}',args.output)
                print('BEST',i,best,kind,flush=True)
            rr.pop('table',None);rr.pop('emission',None)
            rr.update(index=i,mutation=[n,e,kind]);results.append(rr);counts[rr['outcome']]+=1
            if i%10==0:print('SINGLE',i,dict(counts),'best',best,'sec',round(time.monotonic()-begun,1),flush=True)
            (args.output/'single_results.json').write_text(json.dumps(dict(best_states=best,counts=counts,results=results),indent=2)+'\n')
    else:
        rng=random.Random(args.seed);nn,r,oo=NODES,ROOT,origins;bestcost=len(nn);history=[]
        tested=set()
        for i in range(args.iterations):
            n,e,kind=rng.choice(rotate.options(nn));cn,cr,co=mutate(nn,r,n,e,oo);zm=rotate.zero_metrics(cn,cr)
            if zm[1]>7 or zm[2]>39:continue
            cost=len(cn);temperature=.05+.4*(1-(i%5000)/5000)
            if cost<=len(nn) or rng.random()<math.exp((len(nn)-cost)/temperature):
                nn,r,oo=cn,cr,co;history.append([n,e,kind])
            if cost<bestcost:
                bestcost=cost
                (args.output/'best_grammar.json').write_text(json.dumps(dict(root=cr,nodes=cn,origins={q:sorted(v) for q,v in co.items()},history=history),indent=2)+'\n')
                print('GRAMMAR',i,cost,'sec',round(time.monotonic()-begun,1),flush=True)
            if cost<=201 and i%10==0:
                fp=fingerprints(cn)[cr]
                if fp in tested:continue
                tested.add(fp);rr=evaluate(cn,cr,co,args.allocation,args.boot_limit)
                if rr.get('working_states',999)<best:
                    best=rr['working_states'];save_candidate(rr,cn,cr,co,f'best_{i}_{best}',args.output)
                    print('BEST',i,best,kind,flush=True)
                rr.pop('table',None);rr.pop('emission',None);rr.update(index=i)
                results.append(rr);counts[rr['outcome']]+=1
                print('CHECK',i,cost,rr['outcome'],rr.get('working_states'),dict(counts),flush=True)
            if i%1000==0:
                (args.output/'anneal_results.json').write_text(json.dumps(dict(best_states=best,best_grammar=bestcost,counts=counts,results=results),indent=2)+'\n')
                print('ANNEAL',i,'current',len(nn),'best',bestcost,'sec',round(time.monotonic()-begun,1),flush=True)
        (args.output/'anneal_results.json').write_text(json.dumps(dict(best_states=best,best_grammar=bestcost,counts=counts,results=results),indent=2)+'\n')
    print('FINISHED',dict(counts),'best',best,'sec',round(time.monotonic()-begun,1),flush=True)

if __name__=='__main__':main()
