#!/usr/bin/env python3
"""Cost original, equality-bearing AX under exact schema/layout changes.

No axiom is deleted or dualized. Each logical row independently permutes its
arbitrary scalar parameters. The sole stream-read parameter u is kept at one
occurrence in rho8. Conjunction factors are commuted and reassociated only.
Weighted Re-Pair is attributed to the supplied one-schema research package.
Writes only --output. This is an engineering experiment, not a ZFC endpoint.
"""
from __future__ import annotations
import argparse, copy, hashlib, importlib, itertools, json, math, random, sys, time
from pathlib import Path

def rename(f, perm):
    if isinstance(f, tuple):
        return (f[0], rename(f[1], perm), rename(f[2], perm))
    return perm.get(f, f)

def and_parts(f):
    if isinstance(f, tuple) and f[0] == 'imp' and f[2] == 1:
        a = f[1]
        if isinstance(a, tuple) and a[0] == 'imp':
            b = a[2]
            if isinstance(b, tuple) and b[0] == 'imp' and b[2] == 1:
                return a[1], b[1]
    return None

def variants(f, t):
    parts = and_parts(f)
    if parts:
        return [out for a,b in itertools.product(variants(parts[0],t), variants(parts[1],t))
                for out in (t.And(a,b), t.And(b,a))]
    if isinstance(f, tuple):
        return [(f[0],a,b) for a,b in itertools.product(variants(f[1],t),variants(f[2],t))]
    return [f]

def trees(items, t):
    if len(items)==1: return items
    return [t.And(a,b) for cut in range(1,len(items))
            for a,b in itertools.product(trees(items[:cut],t),trees(items[cut:],t))]

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--prior',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--iterations',type=int,default=20000)
    ap.add_argument('--rng-seed',type=int,default=10616)
    ap.add_argument('--conjunction-grid',action='store_true')
    args=ap.parse_args()
    repo=args.repo.resolve(); prior=args.prior.resolve(); out=args.output.resolve()
    assert out != repo and repo not in out.parents
    out.mkdir(parents=True,exist_ok=True)
    research=repo/'Computability/BusyBeaver/Research/ZFC'
    sys.path[:0]=[str(research),str(prior)]
    import theory_backend_experiment as t
    import recover_wade_dag as r
    import rebracket_axioms as g
    from audit_raw_candidate import normalize_named
    nodes,names=r.parse_dag(r.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
    t.old_contract(nodes)
    spec,specsha=t.published_spec()
    rows=spec['ax_rows']('a','h','b','c','u')
    permutations=[dict(zip(('a','b','c'),p)) for p in itertools.permutations(('a','b','c'))]
    lukperms=[dict(zip(('a','b','c','u'),p)) for p in itertools.permutations(('a','b','c','u'))
              if p[0]!='u' and p[2]!='u']
    assert len(lukperms)==12
    C=variants(spec['bundle_C']('a','b','c'),t)
    G=variants(spec['bundle_G']('a','b','c'),t)
    V=[t.Imp(rel('a','b'),t.All('c',rel('a','b'))) for rel in (t.Rel,t.Eq)]
    toporders=list(itertools.permutations(range(4)))
    rowvariants={i:[rename(rows[i],p) for p in (lukperms if i==1 else permutations)]
                 for i in range(1,9)}
    for v in rowvariants[1]: assert t.emit(v).count(158)==1
    def program(d):
        fs=[rowvariants[i][d['perms'][i-1]] for i in d['order']]
        components=[C[d['C']],G[d['G']],*V]
        bundle=trees([components[i] for i in toporders[d['outer_order']]],t)[d['tree']]
        word=[166,121,180,176]+[m for f in fs for m in t.emit(f)]+t.emit(bundle)+t.TAIL
        actual,_=t.symbolic(word)
        assert actual==['old_top',t.All('a','h'),*fs,bundle]
        return word, fs, bundle
    cache={}
    def coarsen(word):
        # Retain the original closed macro node161, exactly push-a ; implication.
        out=[]; i=0
        while i<len(word):
            if word[i:i+2]==[166,119]: out.append(161);i+=2
            else: out.append(word[i]);i+=1
        return out
    def evaluate(d):
        word,_,_=program(d)
        key=(tuple(word),d['seed'],d['alpha'])
        if key in cache: return cache[key]
        seq,gr=g.repair(coarsen(word),d['seed'],d['alpha'])
        nn,_,_=g.transform(nodes,names,seq,gr)
        value=len(nn)+62
        if len(cache)<300000: cache[key]=value
        return value
    initial={'order':list(range(1,9)),'perms':[0]*8,'C':0,'G':0,
             'outer_order':0,'tree':2,'seed':341,'alpha':4}
    # Tree 2 is ((C AND G) AND (Vr AND Ve)), the original four-factor bundle.
    assert program(initial)[0]==t.expand(nodes,1)
    rng=random.Random(args.rng_seed)
    best=copy.deepcopy(initial); bestv=evaluate(best)
    current=copy.deepcopy(best); cv=bestv
    records=[{'iteration':0,'states':bestv,'recipe':copy.deepcopy(best)}]
    print(json.dumps(records[-1]),flush=True)
    start=time.monotonic()
    for it in range(1,args.iterations+1):
        if it%2000==0:
            current=copy.deepcopy(best);cv=bestv
        candidate=copy.deepcopy(current)
        kind=rng.randrange(8)
        if kind==0:
            i,j=rng.sample(range(8),2)
            candidate['order'][i],candidate['order'][j]=candidate['order'][j],candidate['order'][i]
        elif kind==1:
            i=rng.randrange(8)
            candidate['perms'][i]=rng.randrange(len(rowvariants[i+1]))
        elif kind==2: candidate['C']=rng.randrange(len(C))
        elif kind==3: candidate['G']=rng.randrange(len(G))
        elif kind==4: candidate['outer_order']=rng.randrange(len(toporders))
        elif kind==5: candidate['tree']=rng.randrange(5)
        elif kind==6: candidate['seed']=rng.randrange(2048)
        else: candidate['alpha']=rng.choice([1,2,4,8])
        value=evaluate(candidate)
        temp=.35+1.2*(1-(it%2000)/2000)
        if value<=cv or rng.random()<math.exp((cv-value)/temp):
            current,cv=candidate,value
        if value<bestv:
            best,bestv=copy.deepcopy(candidate),value
            records.append({'iteration':it,'states':bestv,'recipe':copy.deepcopy(best)})
            print(json.dumps(records[-1]),flush=True)
        if it%5000==0:
            print(json.dumps({'iteration':it,'best':bestv,'elapsed':time.monotonic()-start}),flush=True)
    grid_cases=0
    if args.conjunction_grid:
        for ci,gi,oi,ti,seed,alpha in itertools.product(range(8),range(4),range(24),range(5),
                                                     (341,181,122,93,39,240,1195),(2,4)):
            candidate=copy.deepcopy(initial)
            candidate.update(C=ci,G=gi,outer_order=oi,tree=ti,seed=seed,alpha=alpha)
            value=evaluate(candidate);grid_cases+=1
            if value<bestv:
                best,bestv=copy.deepcopy(candidate),value
                records.append({'conjunction_grid_case':grid_cases,'states':bestv,'recipe':copy.deepcopy(best)})
                print(json.dumps(records[-1]),flush=True)
            if grid_cases%10000==0:
                print(json.dumps({'conjunction_grid_case':grid_cases,'best':bestv}),flush=True)
    word,fs,bundle=program(best)
    assert all(g.bounder(nodes)(f'ENode {q}')==(0,0) for q in set(word))
    seq,gr=g.repair(coarsen(word),best['seed'],best['alpha'])
    nn,nm,ax=g.transform(nodes,names,seq,gr)
    backenddir=out/'backend';backenddir.mkdir(exist_ok=True)
    for fn in ('TMBuilder.py','tm.py','tmdb.py','LICENSE.wade'):
        (backenddir/fn).write_bytes(r.git_bytes(None,'ZF/generator/'+fn))
    sys.path.insert(0,str(backenddir));backend=importlib.import_module('TMBuilder')
    machine=g.compile_dag(backend,nn,nm);g.reextract(machine,nn,nm)
    named=out/'full_logic_best.named.tm';machine.save(str(named))
    numeric,labels,meta=normalize_named(named.read_bytes())
    (out/'full_logic_best.tm').write_bytes(numeric)
    (out/'full_logic_best.labels.json').write_text(json.dumps(labels,indent=2)+'\n')
    assert meta['working_states']==bestv
    (out/'full_logic_best.dag.json').write_text(json.dumps({'nodes':nn,'names':nm,'root':0,'axioms_root':ax},indent=2)+'\n')
    # Build a directly emitted reference of exactly the same revised word.
    b=r.builder_from_dag(backend,nodes,names)
    b.sequence_lookup={s.seq:i for i,s in enumerate(b.sequences)}
    t.lower_program(b,nodes,word,'full_logic_layout',shared=True)
    def builder_dag(builder):
        reachable=set(builder.reachable());root=builder.find_seq('main().0')
        order=[root]+sorted(reachable-{root});ids={q:i for i,q in enumerate(order)}
        def edge(x):
            if isinstance(x,int):return f'ENode {ids[x]}'
            if x=='halt':return 'EHalt'
            if x.startswith('_'):
                return ('EBreak ' if x.startswith('_break.') else 'EContinue ')+x.rsplit('.',1)[1]
            _,reg,op=x.split('.')
            return ('EInc ' if op=='inc' else 'EDecnz ')+str(r.REGISTERS.index(reg))
        return {ids[q]:tuple(edge(x) for x in builder.sequences[q].seq) for q in order}, {ids[q]:builder.sequences[q].name for q in order}
    ref,refnames=builder_dag(b)
    cert,stats=g.bisimulation(ref,nn)
    (out/'full_logic_reference.dag.json').write_text(json.dumps({'nodes':ref,'names':refnames,'root':0},indent=2)+'\n')
    (out/'full_logic_rm_certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
    evidence={'source_pin':'47f3a3602946dfe48803a91a910c646e74637ac8',
              'spec_sha256':specsha,'upstream_pin':r.COMMIT,'iterations':args.iterations,
              'rng_seed':args.rng_seed,'elapsed_seconds':time.monotonic()-start,
              'conjunction_grid_cases':grid_cases,
              'full_original_equality_logic_retained':True,'old_rho6_retained':True,
              'original_base4_codec_retained':True,'logical_row_order':[9-i for i in best['order']],
              'logical_parameter_permutations':{
                  str(9-i):(lukperms if i==1 else permutations)[best['perms'][i-1]] for i in range(1,9)},
              'logical_rows_ast':fs,'theory_bundle_ast':bundle,'macro_word':word,
              'recipe':best,'improvements':records,'table':meta,
              'rm_bisimulation':stats,'grammar_productions':len(gr),'residual_length':len(seq),
              'complete_binary_compiler_proved':False,'new_ZFC_bound_claimed':False,
              'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'prior_repair_sha256':hashlib.sha256((prior/'rebracket_axioms.py').read_bytes()).hexdigest()}
    (out/'full_logic_results.json').write_text(json.dumps(evidence,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'final_working_states':bestv,'decisions':len(nn),'rm_certificate_pairs':len(cert['pairs'])}),flush=True)

if __name__=='__main__':main()
