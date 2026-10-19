#!/usr/bin/env python3
"""Measure fixed-variable C/G axiom-emitter alternatives; no equivalence asserted.
New compiler/glue by this experiment. Attributed unchanged helpers and Wade MIT-0
backend come from pinned ProveIt 7ba1598461c6e485c5aeb8f673c0b1d571f8012b.
"""
from pathlib import Path
import sys, json, time, itertools, argparse, importlib, hashlib
from collections import Counter
HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'source'
R=SOURCE/'Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0,str(R))
import recover_wade_dag as recover
import theory_backend_experiment as t
import full_grammar_experiment as common
import layout_grammar_experiment as lg
H=common.load_file('fixed_helper',common.REPORT/'code/08-schema-machine-rebracket_axioms.py')
L=common.load_file('fixed_layout',common.REPORT/'code/19-subst-engineering-full_logic_search.py')
N,NAMES=recover.parse_dag(recover.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
SPEC,_=t.published_spec(); OLD,PREFIX,_=t.old_contract(N)
INC=-1

def emit(f,k):
    if f=='k':return [168]+[INC]*k
    if f==2:return [177,INC]
    if not isinstance(f,tuple):return t.emit(f)
    if f[0]=='imp' and f[2]==1:
        a=f[1]
        if isinstance(a,tuple) and a[0] in ('imp','all') and isinstance(a[2],tuple) and a[2][0]=='imp' and a[2][2]==1:
            return emit(a[1],k)+emit(a[2][1],k)+[178 if a[0]=='imp' else 183]
        return emit(a,k)+[218]
    kind,a,b=f
    return emit(a,k)+emit(b,k)+[dict(imp=119,rel=181,eq=182,all=180)[kind]]

def symbolic(word,k):
    stack=['old_top'];b='h';u=None;ev=[]
    for m in word:
        if m==INC:
            x=stack.pop()
            stack.append(x+1 if isinstance(x,int) else ('succ',x))
        elif m in (166,121,168,171,177):stack.append({166:'a',121:b,168:'c',171:0,177:1}[m])
        elif m in (119,181,182,180,178,183):
            y,x=stack.pop(),stack.pop();stack.append({119:t.Imp,181:t.Rel,182:t.Eq,180:t.All,178:t.And,183:t.Ex}[m](x,y))
        elif m==218:stack[-1]=t.Not(stack[-1])
        elif m==176:b='b';ev.append('read_b')
        elif m==158:u='u'
        elif m==208:
            assert stack[-1]==0 and u=='u';stack[-1]='u';u=None
        elif m in t.TAIL:ev.append(t.MACROS[m])
        else:raise ValueError(m)
    return stack,ev

def replacek(f,k):
    if f=='k':
        f='c'
        for _ in range(k):f=('succ',f)
        return f
    return (f[0],replacek(f[1],k),replacek(f[2],k)) if isinstance(f,tuple) else f

def coarsen(word):
    seq=[];i=0
    while i<len(word):
        if word[i:i+2]==[166,119]:seq.append(161);i+=2
        else:seq.append(word[i]);i+=1
    return seq

def transform(tokens,seq,grammar):
    # Like attributed layout transform, but an INC terminal is a literal edge.
    keep={q for q in N if not 1<=q<=114};todo=[q for q in tokens if q>=0 and q not in keep]
    while todo:
        q=todo.pop()
        if q in keep:continue
        keep.add(q);todo += [int(e.split()[1]) for e in N[q] if e.startswith('ENode ')]
    nn={q:N[q] for q in keep};names={q:NAMES[q] for q in keep};intern={es:q for q,es in nn.items()};refs={};nextid=max(N)+1
    def edge(q):return 'EInc 1' if q==INC else refs.get(q,f'ENode {q}')
    def pair(a,b):
        nonlocal nextid
        es=a,b
        if es not in intern:
            intern[es]=nextid;nn[nextid]=es;names[nextid]=f'fixed_axiom_{nextid}';nextid+=1
        return f'ENode {intern[es]}'
    for j,(a,b) in enumerate(grammar):refs[300+j]=pair(edge(a),edge(b))
    root=edge(seq[-1])
    for a in reversed(seq[:-1]):root=pair(edge(a),root)
    for q in list(nn):nn[q]=tuple(root if e=='ENode 1' else e for e in nn[q])
    seen=set();todo=[0]
    while todo:
        q=todo.pop()
        if q in seen:continue
        seen.add(q);todo += [int(e.split()[1]) for e in nn[q] if e.startswith('ENode ')]
    order=[0]+sorted(seen-{0});ids={q:i for i,q in enumerate(order)}
    return ({ids[q]:tuple(f'ENode {ids[int(e.split()[1])]}' if e.startswith('ENode ') else e for e in nn[q]) for q in order},{ids[q]:names[q] for q in order})

def components(mode):
    C=SPEC['bundle_C'](0,1,2) if mode in ('Cfixed','both') else SPEC['bundle_C']('a','b','c')
    if mode in ('Gfixed','both'):
        w=t.Ex(1,t.And('c',t.Rel(1,'k')))
        G=t.Ex('k',t.And(t.All(0,t.Imp(t.Rel(0,1),t.All(1,t.Imp('c',w)))),t.All(1,t.Imp(t.Rel(1,'k'),t.Ex(0,'c')))))
    else:G=SPEC['bundle_G']('a','b','c')
    V=[t.Imp(rel('a','b'),t.All('c',rel('a','b'))) for rel in (t.Rel,t.Eq)]
    return L.variants(C,t),L.variants(G,t),V

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seeds',type=int,default=100);ap.add_argument('--grid',action='store_true');ap.add_argument('--dual',action='store_true');ap.add_argument('--double-b6',action='store_true');ap.add_argument('--tag-swap',action='store_true');ap.add_argument('--mp-first',action='store_true');ap.add_argument('--output',type=Path,default=HERE/'fixed_axioms');args=ap.parse_args()
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=True);backenddir=out/'backend';backenddir.mkdir(exist_ok=True)
    for name in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade'):(backenddir/name).write_bytes(recover.git_bytes(None,'ZF/generator/'+name))
    sys.path.insert(0,str(backenddir));backend=importlib.import_module('TMBuilder')
    if args.tag_swap:
        N[180],N[182]=N[182],N[180]
    if args.mp_first:
        N[147]=('ENode 148','ENode 221')
        N[221]=('ENode 199','ENode 170');NAMES[221]='nip_clear_then_pop'
        N[130]=('ENode 123','ENode 219')
        N[219]=('ENode 198','ENode 220');NAMES[219]='mp_goal_copy_and_test'
        N[220]=('EInc 5','ENode 132');NAMES[220]='mp_goal_one_test'
    original=H.compile_dag(backend,N,NAMES)
    live={q for q in N if (NAMES[q],'0') in original.states}
    H.reextract(original,{q:N[q] for q in live},{q:NAMES[q] for q in live})
    assert len({q for q,b in original.states})==(282 if args.mp_first else 281)
    results={};started=time.monotonic()
    for mode,k in ([('original',1)] if args.tag_swap or args.mp_first or args.double_b6 else [(f'dual_efq_{v}',1) for v in ('a','b','c')] if args.dual else [('original',1),('Cfixed',1),('Gfixed',1),('Gfixed',2),('both',1),('both',2)]):
        C,G,V=components(mode);best=None;trials=0;hist=Counter();framework_checks={}
        recipes=list(itertools.product(range(len(C)),range(len(G)),range(24),range(5))) if args.grid else [(2,1,16,1)]
        for ci,gi,oi,ti in recipes:
            order=list(itertools.permutations(range(4)))[oi];fs=[C[ci],G[gi],*V];bundle=L.trees([fs[i] for i in order],t)[ti]
            rows=SPEC['ax_rows']('a','h','b','c','u')
            if args.double_b6:
                assert rows[5]==t.Imp(t.All('a',t.All('b','c')),t.All('b',t.All('a','c')))
                rows[5]=t.Imp(t.Ex('a',t.Ex('b',t.All('a',t.All('b','c')))),'c')
            if mode.startswith('dual_efq_'):
                rows[3]=t.Imp('b',t.All('a',t.Ex('a','b')))
                rows.append(t.Imp(1,mode[-1]))
            prefix=([166,121,180,176]+[m for f in rows[1:] for m in emit(f,k)])
            word=prefix+emit(bundle,k)+t.TAIL
            stack,ev=symbolic(word,k)
            expected=['old_top']+rows+[replacek(bundle,k)]
            assert stack==expected,(mode,k,'symbolic emission mismatch')
            tokens=coarsen(word)
            assert all(q==INC or H.bounder(N)(f'ENode {q}')==(0,0) for q in tokens)
            for exp in [2,4,8]:
                for seed in range(args.seeds):
                    seq,grammar,_=common.safe_repair(tokens,seed,exp)
                    assert common.expand(seq,grammar)==tokens
                    nn,nm=transform(tokens,seq,grammar);depth=lg.dispatch_depth(nn)
                    # Every previously used opcode/read-side remains, except EInc1 may occur on0.
                    # Check actual framework for every distinct leaf signature/depth before scoring.
                    sig=(tuple(sorted(lg.framework_leaves(nn))),depth)
                    if sig not in framework_checks:
                        m=H.compile_dag(backend,nn,nm);H.reextract(m,nn,nm)
                        fw=len({q for q,b in m.states})-len(nn);framework_checks[sig]=fw
                    cost=len(nn)+framework_checks[sig];hist[cost]+=1;trials+=1
                    key=(cost,len(nn),depth,len(grammar),len(seq),ci,gi,oi,ti,seed,exp)
                    if best is None or key<best['key']:
                        best=dict(key=key,nodes=nn,names=nm,word=word,tokens=tokens,residual=seq,grammar=grammar,bundle=bundle)
                        print(json.dumps(dict(mode=mode,k=k,minimum_states=cost,nodes=len(nn),depth=depth,trials=trials,recipe=key[5:])),flush=True)
        dest=out/f'{mode}_k{k}';dest.mkdir(exist_ok=True)
        m=H.compile_dag(backend,best['nodes'],best['names']);H.reextract(m,best['nodes'],best['names'])
        data,labels,missing=common.normalize(m);(dest/'candidate.tm').write_bytes(data);m.save(str(dest/'candidate.named.tm'))
        (dest/'grammar.json').write_text(json.dumps({x:best[x] for x in ('word','tokens','residual','grammar','bundle')},indent=2)+'\n')
        (dest/'dag.json').write_text(json.dumps(dict(root=0,nodes=best['nodes'],names=best['names']),indent=2)+'\n')
        results[f'{mode}_k{k}']=dict(working_states=best['key'][0],decision_nodes=len(best['nodes']),best_key=best['key'],trials=trials,histogram=hist,sha256=hashlib.sha256(data).hexdigest(),transition_rows=len(data.decode().splitlines())-1,missing_totalized=missing,all_edges_reextracted=True,symbolic_AXIOM_emission_checked=True,calibration_proved=False)
        (out/'results.json').write_text(json.dumps(dict(pin='7ba1598461c6e485c5aeb8f673c0b1d571f8012b',results=results,seconds=time.monotonic()-started),indent=2)+'\n')
    print(json.dumps(results,indent=2))
if __name__=='__main__':main()
