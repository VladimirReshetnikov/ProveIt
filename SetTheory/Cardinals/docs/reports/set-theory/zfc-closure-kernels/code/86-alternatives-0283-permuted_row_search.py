#!/usr/bin/env python3
"""Cost exact reparameterizations of universally emitted logical row schemas.
Changes no theory bundle, gates or logical axiom family. Output is experimental,
not a verified source-to-binary consistency theorem. See sibling report.
"""
from pathlib import Path
import sys,json,itertools,importlib,time,hashlib,random,argparse
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'machine_encoding'))
import specialized_axiom_compiler as s

def remap(f,p):
    return (f[0],remap(f[1],p),remap(f[2],p)) if isinstance(f,tuple) else p.get(f,f)
def count(f,v):
    return count(f[1],v)+count(f[2],v) if isinstance(f,tuple) else int(f==v)
def run(args):
    out=HERE/'permuted_rows';out.mkdir(exist_ok=True);bd=out/'backend';bd.mkdir(exist_ok=True)
    for name in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade'):(bd/name).write_bytes(s.recover.git_bytes(None,'ZF/generator/'+name))
    sys.path.insert(0,str(bd));backend=importlib.import_module('TMBuilder')
    old=s.SPEC['ax_rows']('a','h','b','c','u'); options={}
    for i in range(1,9):
        labels=('a','b','c','u') if i==1 else ('a','b','c')
        opts=[]
        for perm in itertools.permutations(labels):
            mp=dict(zip(labels,perm));f=remap(old[i],mp)
            if i==1 and count(f,'u')!=1:continue
            if f not in [x[0] for x in opts]:opts.append((f,mp))
        # Original row first, so each index0 denotes unchanged source.
        opts.sort(key=lambda x:x[0]!=old[i]);options[i]=opts
    C,G,V=s.components('original');fs=[C[2],G[1],*V];order=list(itertools.permutations(range(4)))[16]
    bundle=s.L.trees([fs[i] for i in order],s.t)[1]
    cache={};framework={};trials=0;best=None;start=time.monotonic();trace=[]
    seeds=[56]+list(range(args.seeds)); seeds=list(dict.fromkeys(seeds))
    def eval_(choices,deep=False):
        nonlocal trials,best
        key=tuple(choices)
        if key in cache and not deep:return cache[key]
        rows=[old[0]]+[options[i][choices[i-1]][0] for i in range(1,9)]
        word=[166,121,180,176]+[m for r in rows[1:] for m in s.emit(r,1)]+s.emit(bundle,1)+s.t.TAIL
        got,_=s.symbolic(word,1);assert got==['old_top']+rows+[bundle]
        tokens=s.coarsen(word);local=None
        for seed,exp in itertools.product(range(args.deep_seeds) if deep else seeds,(2,4,8)):
            seq,grammar,_=s.common.safe_repair(tokens,seed,exp);assert s.common.expand(seq,grammar)==tokens
            nn,nm=s.transform(tokens,seq,grammar);depth=s.lg.dispatch_depth(nn)
            sig=(tuple(sorted(s.lg.framework_leaves(nn))),depth)
            if sig not in framework:
                machine=s.H.compile_dag(backend,nn,nm);s.H.reextract(machine,nn,nm);framework[sig]=len({q for q,b in machine.states})-len(nn)
            cost=len(nn)+framework[sig];metric=(cost,len(nn),depth,len(grammar),len(seq),seed,exp);trials+=1
            rec=dict(metric=metric,choices=list(choices),nodes=nn,names=nm,word=word,tokens=tokens,rows=rows,grammar=grammar,residual=seq)
            if local is None or metric<local['metric']:local=rec
            if best is None or metric<best['metric']:
                best=rec;msg=dict(best_states=cost,nodes=len(nn),depth=depth,choices=list(choices),trials=trials,seconds=time.monotonic()-start);trace.append(msg);print(json.dumps(msg),flush=True)
        if key not in cache or local['metric']<cache[key]['metric']:cache[key]=local
        return cache[key]
    rnd=random.Random(20261018)
    starts=[[0]*8]+[[rnd.randrange(len(options[i])) for i in range(1,9)] for _ in range(args.restarts)]
    for initial in starts:
        current=eval_(initial)
        for passnum in range(args.passes):
            before=current['metric']
            order=list(range(8));rnd.shuffle(order)
            for j in order:
                candidates=[]
                for k in range(len(options[j+1])):
                    ch=current['choices'].copy();ch[j]=k;candidates.append(eval_(ch))
                current=min(candidates,key=lambda r:r['metric'])
            if current['metric']==before:break
    shortlist=sorted(cache.values(),key=lambda r:r['metric'])[:args.deep_top]
    for r in shortlist:eval_(r['choices'],True)
    machine=s.H.compile_dag(backend,best['nodes'],best['names']);s.H.reextract(machine,best['nodes'],best['names']);data,labels,missing=s.common.normalize(machine)
    (out/'candidate.tm').write_bytes(data);machine.save(str(out/'candidate.named.tm'))
    (out/'best.json').write_text(json.dumps(best,indent=2)+'\n')
    result=dict(pin='7ba1598461c6e485c5aeb8f673c0b1d571f8012b',working_states=best['metric'][0],decision_nodes=len(best['nodes']),metric=best['metric'],choices=best['choices'],parameter_maps={i:options[i][best['choices'][i-1]][1] for i in range(1,9)},formula_sets_preserved_by_bijections=True,u_field_read_count=1,symbolic_AXIOM_emission_checked=True,all_edges_reextracted=True,transition_rows=len(data.decode().splitlines())-1,missing_totalized=missing,sha256=hashlib.sha256(data).hexdigest(),layouts_tested=len(cache),grammar_trials=trials,seconds=time.monotonic()-start,trace=trace,status='Exact-schema source optimization, not a certified binary consistency endpoint.')
    (out/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':
    if not __debug__: raise RuntimeError('Run without -O: assertions are part of these diagnostics.')
    p=argparse.ArgumentParser();p.add_argument('--seeds',type=int,default=8);p.add_argument('--restarts',type=int,default=2);p.add_argument('--passes',type=int,default=2);p.add_argument('--deep-top',type=int,default=8);p.add_argument('--deep-seeds',type=int,default=1000);run(p.parse_args())
