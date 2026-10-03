#!/usr/bin/env python3
"""Independent source-pinned guard projection and sparse schedule audit."""
import argparse
from collections import Counter
from contextlib import contextmanager
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys

PINS={'numeric/compile_packet.py': '2df8a5b96630a9b343266ded0b26b6489be601acdee6f50d2a06dad4563e5f57', 'numeric/MORITA_18_SIGNAL_MACHINE.json': '3f45f8aa2fbf5756cd1e4cf22fa3e55582abc9ba8275fe246652ceb94eb08e05', 'code/quadratic_packet.py': '96d4c2b634d465dfcd4df421d57d7f71da44efa201d00fa2518660e600507eef'}

def need(ok,msg):
    if not ok:raise ValueError(msg)
def exact(a,b):
    if type(a) is not type(b):return False
    if type(a) is dict:return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a) in (list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

@contextmanager
def modules(root):
    paths={'_independent_signal_numeric':'numeric/compile_packet.py','_independent_signal_schema':'code/quadratic_packet.py'}
    present={n:n in sys.modules for n in paths};saved={n:sys.modules.get(n) for n in paths}
    try:
        out=[]
        for n,rel in paths.items():
            spec=importlib.util.spec_from_file_location(n,root/rel);m=importlib.util.module_from_spec(spec);sys.modules[n]=m;exec(compile((root/rel).read_bytes(),str(root/rel),'exec'),m.__dict__);out.append(m)
        yield out
    finally:
        for n in paths:
            sys.modules.pop(n,None)
            if present[n]:sys.modules[n]=saved[n]

def canonical(row):
    d={}
    for i,c in row:d[i]=d.get(i,0)+c
    return sorted((i,c) for i,c in d.items() if c)
def value(row,x):return sum(c*x[i] for i,c in row)
def deleted(name,c):
    if name in ('span',):return True
    parts=name.split(':')
    return parts[0]=='germ' or parts[0]=='first' and c[int(parts[1])]<0

def row_cost(row,constant=0):
    need(len(row)>0 and len({i for i,c in row})==len(row) and all(type(c) is int and c!=0 for i,c in row),'Noncanonical affine row')
    need(any(c>0 for _,c in row),'Schedule requires one positive starting term')
    return Counter(M=sum(abs(c)>1 for _,c in row),A=len(row)-1+int(constant!=0),nnz=len(row),rows=1)

def direct_packet(packet,x,y,selectors,copies,slacks):
    B=len(packet);res=[sum(selectors)-1]
    res.extend(x[i]-sum(z[i] for z in copies) for i in range(18))
    res.extend(y[i]-sum(value(p['matrix'][i],copies[r]) for r,p in enumerate(packet)) for i in range(18))
    for r,p in enumerate(packet):
        res.extend(value(row,copies[r]) for _,row in p['eq'])
        res.extend(value(row,copies[r])-selectors[r]-slacks[r][name] for name,row in p['strict'])
    comp=[(sum(selectors)-selectors[r])*sum(copies[r]) for r in range(B)]
    return sum(v*v for v in res)+sum(comp),res,comp

def reduced(p):return dict(p,strict=[(n,row) for n,row in p['strict'] if not deleted(n,p['c'])])
def restore(packet,e,copies,slacks):
    return [dict(s,**{n:value(row,copies[r])-e[r] for n,row in p['strict'] if deleted(n,p['c'])}) for r,(p,s) in enumerate(zip(packet,slacks))]
def graph_construction(p):
    c,J=p['c'],p['J'];h=[c[i] if i in J else max(c[i],0)+1 for i in range(17)]
    return h+[p['source_code']*sum(h)]

def verify(root):
    root=Path(root).resolve()
    for rel,h in PINS.items():need(hashlib.sha256((root/rel).read_bytes()).hexdigest()==h,'Source pin mismatch: '+rel)
    counts=Counter();deleted_kinds=Counter();forms=[];sample={};cost={'old':Counter(),'new':Counter()};T=Counter();R=Counter();matstats=Counter();all_schemas=hashlib.sha256()
    with modules(root) as (m,q):
        C=m.Compiler().close();B=len(C.branches);need((len(C.modes),B)==(49700,80501),'Closure differs')
        selected=set([0,1,B-1,*range(0,B,1291)])
        for r,(s,t,J) in enumerate(C.branches):
            c=C.cs[s];j=J[0];cj=c[j];need(cj>0 and all(c[i]>0 for i in J),'Nonpositive selected speed')
            # Reconstruct every guard and endpoint coefficient from the actual speeds.
            expected_eq=[('mode',[(i,-C.codes[s]) for i in range(17)]+[(17,1)])]+[(f'tie:{i}',canonical([(i,cj),(j,-c[i])])) for i in J[1:]]
            expected_st=[(f'germ:{i}',[(i,1)]) for i in range(17) if c[i]>=0]+[('span',[(i,1) for i in range(17)]),('positive_delay',[(j,1)])]+[(f'first:{i}',canonical([(i,cj),(j,-c[i])])) for i in range(17) if i not in J]
            eq,st=C.guards(s,t,J);need(eq==expected_eq and st==expected_st,'Literal guard coefficient mismatch');counts['actual_branch_guard_formulas']+=1
            matrix=[canonical([(i,cj),(j,-c[i])]) for i in range(17)]
            matrix.append(canonical([(i,C.codes[t]*(cj-(sum(c) if i==j else 0))) for i in range(17)]))
            need(C.matrix(s,t,J)==matrix,'Literal endpoint matrix differs');counts['actual_branch_endpoint_matrices']+=1
            p={'eq':eq,'strict':st,'matrix':matrix,'c':c,'J':J,'source_code':C.codes[s]}
            if r in selected:sample[r]=p
            if s==641 and t==657 and J==(0,2):sample['real']=p
            kept=[];gone=[]
            for name,row in st:
                if deleted(name,c):gone.append(name);deleted_kinds[name.split(':')[0]]+=1
                else:kept.append(name)
            need(len(gone)==18 and kept==['positive_delay']+[f'first:{i}' for i in range(17) if i not in J and c[i]>=0],'Wrong source rows deleted');counts['exact_deletion_schema']+=1
            all_schemas.update(json.dumps([r,eq,st,matrix,gone],separators=(',',':')).encode())
            for tag,ss in (('old',st),('new',[(n,row) for n,row in st if n not in gone])):
                T[tag]+=len(ss);R[tag]+=len(eq)+len(ss)
                for _,row in eq:cost[tag]+=row_cost(row)
                # Local indices 18 and 19 stand for the separate selector/slack.
                for _,row in ss:cost[tag]+=row_cost(row+[(18,-1),(19,-1)])
            matstats['nnz']+=sum(len(row) for row in matrix);matstats['coefficient_M']+=sum(abs(c)>1 for row in matrix for _,c in row)
        # Count the actual global rows independently, including the one constant.
        global_rows=37
        global_nnz=B+18*(B+1)+18+matstats['nnz']
        global_adds=(B-1)+1+18*B+matstats['nnz']
        for tag in ('old','new'):
            cost[tag].update(M=matstats['coefficient_M'],A=global_adds,nnz=global_nnz,rows=global_rows)
            R[tag]+=global_rows;need(cost[tag]['rows']==R[tag],'Row count disagreement')
            cost[tag]['M']+=R[tag]+B
            cost[tag]['A']+=18*B+(R[tag]+B-1)
            cost[tag]['operations']=cost[tag]['M']+cost[tag]['A']
            cost[tag]['strict_slacks']=T[tag];cost[tag]['witnesses']=19*B+T[tag];cost[tag]['degree']=2;cost[tag]['complementarity_products']=B
        need(cost['old']['operations']==25392522 and cost['new']['operations']==17903098,'Complete schedule mismatch')
        need((T['old'],T['new'],R['old'],R['new'])==(2667479,1218461,2762961,1313943),'Source row/slack totals differ')
        rng=random.Random(144019)
        ids=sorted(k for k in sample if type(k) is int)
        for size in (1,2,4,7):
            for start in range(0,len(ids),11):
                keys=[ids[(start+i)%len(ids)] for i in range(size)];packet=[sample[k] for k in keys];child=[reduced(p) for p in packet]
                for rep in range(4):
                    x=[rng.randrange(-9,10) for _ in range(18)];y=[rng.randrange(-9,10) for _ in range(18)];e=[rng.randrange(-3,4) for _ in packet];copies=[[rng.randrange(-5,6) for _ in range(18)] for _ in packet];ss=[{n:rng.randrange(-6,7) for n,row in p['strict']} for p in child]
                    lifted=restore(packet,e,copies,ss);old,oldrows,_=direct_packet(packet,x,y,e,copies,lifted);new,rows,_=direct_packet(child,x,y,e,copies,ss)
                    need(old==new,'Full packet signed graph identity');counts['full_signed_packet_graph_identities']+=1
                # One natural complete zero for every active position, using the actual corrected public evaluator.
                for active in range(size):
                    x=graph_construction(packet[active]);y=[value(row,x) for row in packet[active]['matrix']];e=[int(i==active) for i in range(size)];copies=[x if i==active else [0]*18 for i in range(size)];ss=[{n:value(row,copies[i])-e[i] for n,row in p['strict']} for i,p in enumerate(child)]
                    lifted=restore(packet,e,copies,ss);need(all(v>=0 for d in lifted for v in d.values()),'Natural restored slack negative')
                    need(direct_packet(packet,x,y,e,copies,lifted)[0]==direct_packet(child,x,y,e,copies,ss)[0]==0,'Natural complete packet zero lost');counts['natural_complete_packet_restorations']+=1
                    for pset,w in ((packet,lifted),(child,ss)):
                        branches=[]
                        for p in pset:
                            mm=tuple(tuple(dict(row).get(i,0) for i in range(18)) for row in p['matrix'])
                            gs=tuple(q.Guard(kind,tuple(dict(row).get(i,0) for i in range(18))) for kind,rs in (('eq',p['eq']),('gt',p['strict'])) for name,row in rs)
                            branches.append(q.Branch(mm,gs))
                        witness=(tuple(e),tuple(map(tuple,copies)),tuple(tuple(w[i][n] for n,row in p['strict']) for i,p in enumerate(pset)))
                        need(q.polynomial_value(branches,tuple(x),tuple(y),witness)==0,'Corrected public packet zero differs');counts['corrected_public_packet_zeros']+=1
        p=sample['real'];c,J=p['c'],p['J'];j=J[0];cj=c[j]
        gap=[Fraction(c[i],cj) if i in J else Fraction(max(c[i],0)+cj,cj) for i in range(17)];x=gap+[p['source_code']*sum(gap)];y=[value(row,x) for row in p['matrix']];ch=reduced(p);ss={n:value(row,x)-1 for n,row in ch['strict']}
        need(all(a>=0 for a in x+y) and all(v>=0 for v in ss.values()) and direct_packet([ch],x,y,[1],[x],[ss])[0]==0,'Real reduced counterexample not a complete zero')
        lifted=restore([p],[1],[x],[ss]);need(lifted[0]['germ:2']==Fraction(-1,4),'Real domain counterexample absent');counts['complete_nonnegative_real_counterexample']+=1
    return dict(status='PASS_INDEPENDENT_SIGNAL_GUARD_PROJECTION',source_sha256=PINS,counts=dict(counts),branch_schema_sha256=all_schemas.hexdigest(),removed_by_kind=dict(deleted_kinds),complete_schedule={k:dict(v) for k,v in cost.items()},real_counterexample=dict(branch=[641,657,[0,2]],pivot_speed=12,selected_gap_2='3/4',deleted_germ_slack='-1/4'),scope='Independent exhaustive actual-row/deletion/ledger audit and bounded full-packet graph/public-zero checks. Natural zero-set bijection; signed graph identity. No unchanged-coordinate polynomial equality, nonnegative-real zero-set equivalence, materialized giant SLP or fixed-arity universal operation improvement.')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();out=verify(a.root)
    if a.expect:need(exact(out,json.loads(a.expect.read_text())),'Saved review differs')
    if a.output:a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps(out,indent=2,sort_keys=True))
