#!/usr/bin/env python3
"""Joint closed-block reassociation and physical-register renaming experiment.

Adapted from attributed ProveIt source27's decoder emitter and strict affine
checker. This script emits diagnostic results, not a new formalized theorem.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import argparse, hashlib, json, sys, time
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.modules['cost_search'] = SimpleNamespace()
import strict_affine as strict
import rotate_search as rot

ORIGINAL = HERE.parent/'inputs/zfc_254.tm'
OLD = json.loads((HERE.parent/'inputs/decoder_entries.json').read_text())
NODES = {int(k):tuple(map(tuple,v)) for k,v in OLD['nodes'].items()}
ROOT_NODE = OLD['root']
OLD_FP = {v:int(n) for n,v in OLD['fingerprints'].items()}
PHYS = (6,7,0,2,1,8,4,3,5)
PERM = (0,3,4,5,8,1,6,2,7)
SKIP = (60,44,31,56,38,40,28,64,69)
CORE = {0,1,2,3,4,5,6,7,9,10,13,14,19,20,28,29,30,31,38,40,41,42,43,44,48,56,57,58,59,60,63,64,69,73,74,75,83,84,85,95,97,109,112,131}
BOX_STATES = {0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131}
BOX_PAIRS = {(str(q),b) for q in BOX_STATES for b in (0,1)}-{('3',0)}

def read_table(path):
    out = {}
    for line in path.read_text().splitlines():
        if line and not line.startswith('#'):
            q,b,w,d,t = line.split()
            out[q,int(b)] = (int(w),d,t)
    return out

BASE253 = {k:v for k,v in read_table(ORIGINAL).items() if k[0]!='8'}
BASE253.update({('3',0):(0,'L','48'),('5',0):(1,'R','97'),('5',1):(1,'R','64'),('49',1):(0,'R','5')})
CONTROL_OPTIONS = {}
for n,pair in NODES.items():
    for bit,e in enumerate(pair):
        if e[0] not in ('B','C'): continue
        counts = CONTROL_OPTIONS.setdefault((e,bit), Counter())
        for state,weight in OLD['state_entries'][str(n)].items():
            counts[BASE253[state,bit]] += weight

def fingerprints(nodes):
    @lru_cache(None)
    def fp(e):
        if e[0]=='N':
            a,b=nodes[e[1]]; text='N('+fp(a)+','+fp(b)+')'
        else: text=':'.join(map(str,e))
        return hashlib.sha256(text.encode()).hexdigest()
    return fp

def emit(nodes,root,perm=PERM):
    fp = fingerprints(nodes)
    table = BASE253.copy(); entries={}; allocate=255
    modal=lambda counts:max(counts,key=counts.get)
    for n in nodes:
        f=fp(('N',n))
        if n==root: entries[n]='96'
        elif f in OLD_FP: entries[n]=modal(OLD['state_entries'][str(OLD_FP[f])])
        else: entries[n]=str(allocate);allocate+=1
    def transition(e,bit):
        if e[0]=='N': return bit,'R',entries[e[1]]
        if e[0]=='B' and e[1]==1: return 0,'L','7' if bit==0 else '33'
        if e[0] in ('B','C'): return CONTROL_OPTIONS[e,bit].most_common(1)[0][0]
        return bit,'R',modal(OLD['leaf_entries'][':'.join(map(str,e))])
    for n in nodes:
        if entries[n]=='96' or fp(('N',n)) not in OLD_FP:
            for bit,e in enumerate(nodes[n]): table[entries[n],bit]=transition(e,bit)
    table={k:(w,d,'64' if t=='5' else t) for k,(w,d,t) in table.items() if k[0]!='5'}
    targets={str(SKIP[j]):str(SKIP[perm[j]]) for j in range(9)}
    table={k:(w,d,targets.get(t,t) if int(k[0]) not in CORE else t) for k,(w,d,t) in table.items()}
    return table

def sites(nodes,root):
    output=[];todo=[(('N',root),'')]
    while todo:
        e,p=todo.pop();k=e[0]
        if k=='N':
            a,b=nodes[e[1]];todo.extend([(b,p+'1'),(a,p+'0')])
        else: output.append((p,'C'+k,None if k=='H' else e[1]))
    return output

def inc(p):
    if '0' not in p:return None
    return p[:p.rindex('0')]+'1'

def strip(p,bit,k):
    while k and p:k-=p[-1]==bit;p=p[:-1]
    return p

class Tracking(dict):
    def __init__(self,t):super().__init__(t);self.used=set()
    def __getitem__(self,k):self.used.add(k);return super().__getitem__(k)

def certify(table,nodes,root,perm=PERM):
    assert all(table[p] == BASE253[p] for p in BOX_PAIRS)
    tracked=Tracking(table);count=0;minimum=10**9
    for p,op,r in sites(nodes,root):
        for zero in ((True,False) if op=='CD' else (None,)):
            physical=perm[PHYS[r]] if op in ('CI','CD') else r
            branch=(physical,zero) if op=='CD' else None
            if op=='CI' or op=='CD' and not zero:succ=inc(p)
            elif op=='CD':succ=inc(strip(p,'0',1))
            elif op=='CB':succ=inc(strip(p,'0',r))
            elif op=='CC':succ=strip(p,'1',r)
            else:succ=''
            effect=('inc',physical) if op=='CI' else ('dec',physical) if op=='CD' and not zero else None
            right=([('r',0,1,41),('b',1),('box',('plain',effect))] if succ is None else [('b',int(b)) for b in succ]+[('r',0,1,40-len(succ)),('b',1),('box',('plain',effect))])
            try:
                _,literal=strict.run(tracked,p,branch,strict.canon([('b',1)],right),halt=op=='CH',fuel=1000)
                assert literal>0;minimum=min(minimum,literal);count+=1
            except (AssertionError,KeyError) as e:
                return {'passed':False,'cases_passed':count,'failure':{'path':p,'op':op,'reg':r,'zero':zero,'reason':str(e)}},tracked.used
    return {'passed':True,'cases':count,'min_literal':minimum},tracked.used

def root_frame(q,h,ones):
    if q!='96' or not ones or h-1 not in ones or min(ones)!=h-1:return None
    right=sorted(x for x in ones if x>=h)
    if not right or right[0]-h<40:return None
    gap=right[0]-h;cursor=right[0]+1;high=right[-1];values=[]
    while cursor<=high:
        if cursor in ones:return None
        cursor+=1;n=0
        while cursor in ones:n+=1;cursor+=1
        if not n:return None
        values.append(n-1)
    if len(values)<9 or any(values[:9]):return None
    return {'state':q,'head':h,'gap':gap,'primary':values[:9],'spares':values[9:],'ones':sorted(ones),'all_other_cells_zero':True}

def boot(table,limit):
    q='64';h=0;ones=set();used=set()
    for step in range(limit+1):
        if q=='254':return {'outcome':'halt','steps':step},used
        if q=='96':
            frame=root_frame(q,h,ones)
            if frame is not None:return {'outcome':'zero_root','steps':step,'frame':frame},used
        if step==limit: return {'outcome':'fuel_limit','steps':step,'state':q,'head':h,'one_count':len(ones)},used
        key=q,int(h in ones);used.add(key)
        w,d,q=table[key]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1

def prune(table,used):
    used=used|BOX_PAIRS
    retained={q for q,b in used}|{'64','96'}
    # All Box boundary labels are included even when no literal oracle row
    # accesses them. They are part of the published excursion interfaces.
    retained|={table[k][2] for k in BOX_PAIRS}
    result={}
    for (q,b),(w,d,t) in table.items():
        if q not in retained:continue
        if t not in retained|{'254'}:
            assert (q,b) not in used
            t='64'
        result[q,b]=w,d,t
    assert len(result)==2*len(retained)
    return result

def text_table(table):
    return '#! start 64\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(table.items(),key=lambda x:(int(x[0][0]),x[0][1])))

def main():
    p=argparse.ArgumentParser();p.add_argument('--limit',type=int,default=1000000);p.add_argument('--seconds',type=float,default=400);p.add_argument('--start',type=int,default=0);p.add_argument('--single',type=int);p.add_argument('--runtime-only',action='store_true');p.add_argument('--output',type=Path,default=HERE/'joint_rotation_results.json');a=p.parse_args()
    assert __debug__
    begun=time.monotonic();base=emit(NODES,ROOT_NODE)
    assert base==read_table(HERE.parent/'inputs/permutation252_old.tm')
    cert,used=certify(base,NODES,ROOT_NODE);assert cert['passed'] and cert['cases']==8391
    b,bu=boot(base,a.limit);assert b['outcome']=='zero_root' and b['steps']==82552
    assert len(prune(base,used|bu))==504
    out={'scope':'Joint source27 closed-block reassociation with ProveIt register-permutation252, fixed arbitrary-gap affine rule checker, finite blank prefix. Not a kernel proof.','permutation':PERM,'baseline':{'cert':cert,'boot':b},'options':len(rot.options(NODES)),'results':[]}
    def save():
        out['elapsed_seconds']=time.monotonic()-begun;a.output.write_text(json.dumps(out,indent=2)+'\n')
    for index,(n,e,kind) in enumerate(rot.options(NODES)):
        if index<a.start:continue
        if a.single is not None and index!=a.single:continue
        if time.monotonic()-begun>a.seconds:out['status']='time_limit';save();break
        nodes,root=rot.mutate(NODES,ROOT_NODE,n,e);zm=rot.zero_metrics(nodes,root)
        result={'index':index,'node':n,'operation':kind,'nodes':len(nodes),'shape':zm}
        if zm[1]>7 or zm[2]>39:result['outcome']='shape_bound'
        else:
            try:table=emit(nodes,root)
            except KeyError as ex:result['outcome']='unsupported_leaf';result['exception']=str(ex)
            else:
                c,u=certify(table,nodes,root);result['affine']=c
                if not c['passed']:result['outcome']='affine_failure'
                else:
                    runtime=prune(table,u);result['runtime_states']=len(runtime)//2
                    if a.runtime_only:result['outcome']='runtime_pass'
                    else:
                        b,bu=boot(table,a.limit);result['boot']=b;result['outcome']=b['outcome']
                        if b['outcome']=='zero_root':
                            compact=prune(table,u|bu);result['working_states']=len(compact)//2
                            fname=a.output.parent/f'rotation_{index}_permutation.tm';fname.write_text(text_table(compact));result['table']=fname.name
                            result['sha256']=hashlib.sha256(fname.read_bytes()).hexdigest()
        out['results'].append(result);save()
        print(index,kind,result['outcome'],result.get('runtime_states'),result.get('working_states'),round(time.monotonic()-begun,1),flush=True)
    else:out['status']='complete';save()

if __name__=='__main__':main()
