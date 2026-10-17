#!/usr/bin/env python3
"""Measured alternative complete quantifier basis; no machine calibration claim."""
from pathlib import Path
import argparse,collections,copy,hashlib,importlib.util,itertools,json,random,sys,time

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT/'sources/proveit'
R=REPO/'Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0,str(R))
import recover_wade_dag as r
import theory_backend_experiment as t
from audit_raw_candidate import normalize_named

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    out=importlib.util.module_from_spec(spec);spec.loader.exec_module(out);return out

HOST=REPO/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code'
g=module('prior_grammar',HOST/'19-subst-engineering-vendor-one_schema_machine-rebracket_axioms.py')
f=module('prior_layout',HOST/'19-subst-engineering-full_logic_search.py')

def safe_repair(word,seed,alpha):
    """Weighted Re-Pair counting only disjoint occurrences before selection."""
    rng=random.Random(seed);seq=list(word);gr=[]
    while True:
        raw=collections.Counter(zip(seq,seq[1:]));choices=[]
        for pair,n in raw.items():
            if n<2:continue
            if pair[0]==pair[1]:
                n=0;i=0
                while i+1<len(seq):
                    if tuple(seq[i:i+2])==pair:n+=1;i+=2
                    else:i+=1
            if n>=2:choices.append((pair,n))
        if not choices:break
        pair=rng.choices([p for p,n in choices],[n**alpha for p,n in choices])[0]
        fresh=300+len(gr);new=[];i=0
        while i<len(seq):
            if i+1<len(seq) and tuple(seq[i:i+2])==pair:new.append(fresh);i+=2
            else:new.append(seq[i]);i+=1
        assert len(seq)-len(new)>=2
        seq=new;gr.append(pair)
    return seq,gr

def setup(basis):
    nodes,names=r.parse_dag(r.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
    t.old_contract(nodes)
    spec,_=t.published_spec();rows=spec['ax_rows']('a','h','b','c','u')
    if basis=='protected':
        a,b,c='a','b','c'
        rows[3]=t.Imp(1,b)
        rows[5]=t.Imp(t.Imp(t.All(a,t.All(b,t.Not(t.All(a,t.All(b,c))))),t.All(a,c)),c)
        rows[7]=t.Imp(t.All(a,t.Imp(t.All(a,b),c)),t.Imp(t.All(a,b),t.All(a,c)))
    perms=[dict(zip(('a','b','c'),p)) for p in itertools.permutations(('a','b','c'))]
    luk=[dict(zip(('a','b','c','u'),p)) for p in itertools.permutations(('a','b','c','u')) if p[0]!='u' and p[2]!='u']
    rv={i:[f.rename(rows[i],p) for p in (luk if i==1 else perms)] for i in range(1,9)}
    C=f.variants(spec['bundle_C']('a','b','c'),t);G=f.variants(spec['bundle_G']('a','b','c'),t)
    V=[t.Imp(rel('a','b'),t.All('c',rel('a','b'))) for rel in (t.Rel,t.Eq)]
    orders=list(itertools.permutations(range(4)))
    def word(d):
        fs=[rv[i][d['perms'][i-1]] for i in d['order']]
        parts=[C[d['C']],G[d['G']],*V]
        bundle=f.trees([parts[i] for i in orders[d['outer_order']]],t)[d['tree']]
        w=[166,121,180,176]+[m for a in fs for m in t.emit(a)]+t.emit(bundle)+t.TAIL
        actual,_=t.symbolic(w)
        assert actual==['old_top',t.All('a','h'),*fs,bundle]
        return w,fs,bundle
    def coarse(w):
        out=[];i=0
        while i<len(w):
            if w[i:i+2]==[166,119]:out.append(161);i+=2
            else:out.append(w[i]);i+=1
        return out
    def build(d):
        w,fs,bundle=word(d)
        replacements={178:[218,119,218],183:[218,180,218],218:[177,119]}
        for bit,q in enumerate((178,183,218)):
            if d.get('expand_mask',0)&(1<<bit):
                w=[x for token in w for x in (replacements[q] if token==q else [token])]
        actual,_=t.symbolic(w)
        assert actual==['old_top',t.All('a','h'),*fs,bundle]
        seq,gr=(safe_repair if d['safe'] else g.repair)(coarse(w),d['seed'],d['alpha'])
        nn,nm,ax=g.transform(nodes,names,seq,gr)
        return nn,nm,ax,w,fs,bundle,seq,gr
    return nodes,names,rv,build

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--basis',choices=['original','protected'],default='original')
    ap.add_argument('--iterations',type=int,default=20000);ap.add_argument('--seed',type=int,default=161026)
    ap.add_argument('--recipe',type=Path,help='Replay a recorded recipe JSON (or results.json containing recipe)')
    ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    if not __debug__:ap.error('run without -O: finite checks require assertions')
    if args.iterations < 0:ap.error('--iterations must be nonnegative')
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    nodes,names,rv,build=setup(args.basis)
    selected={'order':list(range(1,9)),'perms':[0]*8,'C':2,'G':1,'outer_order':16,'tree':1,'seed':341,'alpha':4,'safe':False,'expand_mask':0}
    if args.recipe:
        selected=json.loads(args.recipe.read_text())
        if 'basis' in selected and selected['basis']!=args.basis:ap.error('recorded basis does not match --basis')
        selected=selected.get('recipe',selected)
    cache={}
    def cost(nn):
        from functools import cache as memo
        @memo
        def z(q):
            e=nn[q][0]
            return 1+(z(int(e.split()[1])) if e.startswith('ENode ') else 0)
        return len(nn)+55+max(2,max(z(q) for q in nn))
    def evaluate(d):
        key=json.dumps(d,sort_keys=True)
        if key not in cache:cache[key]=cost(build(d)[0])
        return cache[key]
    rng=random.Random(args.seed);best=copy.deepcopy(selected);bv=evaluate(best)
    cur=copy.deepcopy(best);cv=bv;start=time.monotonic();history=[]
    def record(it):
        row={'iteration':it,'states':bv,'recipe':copy.deepcopy(best),'elapsed_seconds':time.monotonic()-start}
        history.append(row);print(json.dumps(row),flush=True)
        (out/'search_checkpoint.json').write_text(json.dumps({'basis':args.basis,'seed':args.seed,'history':history},indent=2)+'\n')
    record(0)
    for it in range(1,args.iterations+1):
        if it%1000==0:cur=copy.deepcopy(best);cv=bv
        cand=copy.deepcopy(cur);kind=rng.randrange(11)
        if kind==0:
            i,j=rng.sample(range(8),2);cand['order'][i],cand['order'][j]=cand['order'][j],cand['order'][i]
        elif kind==1:
            i=rng.randrange(8);cand['perms'][i]=rng.randrange(len(rv[i+1]))
        elif kind==2:cand['C']=rng.randrange(8)
        elif kind==3:cand['G']=rng.randrange(4)
        elif kind==4:cand['outer_order']=rng.randrange(24)
        elif kind==5:cand['tree']=rng.randrange(5)
        elif kind==6:cand['seed']=rng.randrange(16384)
        elif kind==7:cand['alpha']=rng.choice([1,2,4,8,16])
        elif kind==8:cand['safe']=not cand['safe']
        elif kind==9:
            cand['seed']=rng.randrange(16384);cand['safe']=bool(rng.randrange(2))
        else:cand['expand_mask']=rng.randrange(8)
        val=evaluate(cand)
        temp=.25+.8*(1-(it%1000)/1000)
        if val<=cv or rng.random()<__import__('math').exp((cv-val)/temp):cur,cv=cand,val
        if val<bv:best,bv=copy.deepcopy(cand),val;record(it)
        if it%5000==0:print(json.dumps({'iteration':it,'best':bv,'seconds':time.monotonic()-start}),flush=True)
    nn,nm,ax,w,fs,bundle,seq,gr=build(best)
    assert all(g.bounder(nodes)(f'ENode {q}')==(0,0) for q in set(w))
    backenddir=out/'backend';backenddir.mkdir(exist_ok=True)
    for fn in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade'):(backenddir/fn).write_bytes(r.git_bytes(None,'ZF/generator/'+fn))
    sys.path.insert(0,str(backenddir));import TMBuilder as backend
    machine=g.compile_dag(backend,nn,nm);g.reextract(machine,nn,nm)
    named=out/'candidate.named.tm';machine.save(str(named));numeric,labels,meta=normalize_named(named.read_bytes())
    assert meta['working_states']==bv
    (out/'candidate.tm').write_bytes(numeric)
    (out/'candidate.labels.json').write_text(json.dumps(labels,indent=2)+'\n')
    (out/'candidate.dag.json').write_text(json.dumps({'nodes':nn,'names':nm,'root':0,'axioms_root':ax},indent=2)+'\n')
    # A macro expansion check proves the grammar preserves the emitted word.
    expand={q:(q,) for q in range(300)}
    for j,(a,b) in enumerate(gr):expand[300+j]=expand[a]+expand[b]
    coarse=sum((expand[q] for q in seq),())
    expanded=tuple(x for q in coarse for x in ([166,119] if q==161 else [q]))
    assert expanded==tuple(w)
    evidence={'basis':args.basis,'iterations':args.iterations,'search_seed':args.seed,'history':history,'recipe':best,
        'decisions':len(nn),'framework':bv-len(nn),'table':meta,'macro_word':w,'logical_rows_ast':fs,'bundle_ast':bundle,
        'upstream_commit':r.COMMIT,'proveit_commit':'4747142d5d15213eb711bdadfa3cc7e769fcb7a7',
        'grammar_productions':gr,'residual_word':seq,'word_expansion_exact':True,'operation_silent_closed':True,
        'compiled_consistency_proved':False,'record_claimed':False,'elapsed_seconds':time.monotonic()-start}
    (out/'results.json').write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'final_states':bv,'decisions':len(nn),'basis':args.basis}),flush=True)

if __name__=='__main__':main()
