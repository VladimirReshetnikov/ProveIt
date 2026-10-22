"""Locally authored inert-data circuit audit. Never imports repository code."""
import json, pathlib, random, collections
import numpy as np

ROOT=pathlib.Path(__file__).parent
P=65521

def trim(a):
    n=len(a)
    while n>1 and a[n-1]==0:n-=1
    return a[:n]

def operate(op,a,b):
    if op=='*':return trim(np.convolve(a,b)%P)
    n=max(len(a),len(b));c=np.zeros(n,dtype=np.int64)
    c[:len(a)]=a;c[:len(b)]+=b if op=='+' else -b
    return trim(c%P)

def audit(path,j):
    src=j['source'];w=j.get('witnesses',j.get('variables',[]));const=j.get('fixed_numerals',[])
    if not w or not all(isinstance(g,list) and len(g)==4 and g[1] in '+-*' for g in src):return None
    out=[j['output']] if isinstance(j.get('output'),str) else j.get('outputs',[])
    cmp=j.get('comparisons',j.get('equations',[]))
    if cmp and not all(isinstance(c,list) and len(c)==2 for c in cmp):return None
    if not out and not cmp:return None
    counts=collections.Counter(g[1] for g in src)
    rng=random.Random(731928)
    val={x:np.array([0,rng.randrange(1,P)],dtype=np.int64) for x in w}
    val.update({x:np.array([rng.randrange(1,P)],dtype=np.int64) for x in const})
    deg={x:1 for x in w};deg.update({x:0 for x in const})
    deps={}
    def v(x):return np.array([x%P],dtype=np.int64) if isinstance(x,int) else val[x]
    def d(x):return 0 if isinstance(x,int) else deg[x]
    for name,op,a,b in src:
        if name in val:raise ValueError('redefinition '+name)
        val[name]=operate(op,v(a),v(b));deg[name]=d(a)+d(b) if op=='*' else max(d(a),d(b));deps[name]=[a,b]
    roots=out or [x for c in cmp for x in c]
    live=set()
    def walk(x):
        if not isinstance(x,str) or x in live:return
        live.add(x)
        for a in deps.get(x,[]):walk(a)
    for x in roots:walk(x)
    obs=[len(operate('-',v(a),v(b)))-1 for a,b in cmp] if cmp else [len(v(x))-1 for x in out]
    upper=[max(d(a),d(b)) for a,b in cmp] if cmp else [d(x) for x in out]
    stated=j.get('residual_exact_degrees',j.get('residual_degrees')) if cmp else j.get('exact_degree',j.get('degree'))
    ledger=j.get('ledger',{});claim=ledger.get('operations',ledger.get('total'))
    return dict(path=str(path.relative_to(ROOT)),unknowns=len(w),equations=len(cmp) if cmp else len(out),operations=len(src),multiplications=counts['*'],additions_subtractions=counts['+']+counts['-'],declared_operations=claim,operation_count_agrees=claim is None or claim==len(src),all_gates_live=all(g[0] in live for g in src),all_witnesses_live=all(x in live for x in w),all_constants_live=all(x in live for x in const),syntactic_degree_bounds=upper,modular_line_degrees=obs,declared_degrees=stated,degree_agrees=stated is None or (stated==obs if isinstance(stated,list) else [stated]==obs),domain=j.get('witness_domain',j.get('domain','unspecified')))

rows=[]; errors=[]
for p in sorted(ROOT.glob('**/*.json')):
    j=json.loads(p.read_text())
    if isinstance(j,dict) and isinstance(j.get('source'),list):
        try:
            r=audit(p,j)
            if r:rows.append(r)
        except Exception as e:errors.append(dict(path=str(p.relative_to(ROOT)),error=str(e)))
result=dict(scope='Independent literal operation, liveness, syntactic degree and modular-line diagnostic checks. Not a fixed-coefficient degree proof or compiler formalization.',prime=P,rows=rows,errors=errors)
(ROOT/'INDEPENDENT_GATE_AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(circuits=len(rows),errors=errors,discrepancies=[r for r in rows if not all([r['operation_count_agrees'],r['all_gates_live'],r['all_witnesses_live'],r['degree_agrees']])]),indent=2))
