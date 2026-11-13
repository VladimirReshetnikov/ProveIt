#!/usr/bin/env python3
"""Independent top-layer and full-fixed-tuple modular degree proof."""
import collections,gzip,hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';GRAPH=BASE/'research/thirteen-first-norm-correction92/polynomial.json';MASK=BASE/'Lean/DiophantineConsistency/CurrentMaskData2011.lean';KERNEL=BASE/'Lean/DiophantineConsistency/CurrentKernelData2011.lean';P=1000000007
VARS=('J','F','alpha','f','i','T','s','w','n','eta','zeta','m','gamma');PORTS=('beta','K0','MC','MF');SYMS=VARS+PORTS;ZERO=(0,)*len(SYMS)
def need(b,m):
    if not b:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def add(a,b,sgn=1):
    z=a.copy()
    for m,c in b.items():z[m]=z.get(m,0)+sgn*c
    return {m:c for m,c in z.items() if c}
def mul(a,b):
    z=collections.defaultdict(int)
    for x,c in a.items():
        for y,d in b.items():z[tuple(i+j for i,j in zip(x,y))]+=c*d
    return {m:c for m,c in z.items() if c}
def const(n):return {ZERO:n} if n else {}
def symbol(n):
    x=list(ZERO);x[SYMS.index(n)]=1;return {tuple(x):1}
def deg(a):return max((sum(m[:13]) for m in a),default=-1)
def univ(a,b,kind):
    o=[0]*(len(a)+len(b)-1 if kind=='*' else max(len(a),len(b)))
    if kind=='*':
        for i,x in enumerate(a):
            for j,y in enumerate(b):o[i+j]=(o[i+j]+x*y)%P
    else:
        for i,x in enumerate(a):o[i]=(o[i]+x)%P
        for i,x in enumerate(b):o[i]=(o[i]+x*(1 if kind=='+' else -1))%P
    while len(o)>1 and o[-1]==0:o.pop()
    return o
def main():
    blob=subprocess.run(['git','show','20c4dd9d3c:'+GRAPH.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
    need(hashlib.sha256(blob).hexdigest()==sha(GRAPH)=='a214fc19ea776e4e3880e13a7cd92260e76e71588c8c6b391669007a180ab3be','graph provenance')
    need(sha(MASK)=='8e92c1f507bc250c31fb2671a921dfbef7a44ba643956f962cd64d9b50bd4582' and sha(KERNEL)=='529b2f89e4e93516a8a52343d98dc749c57f5a967d8ef522b92373bf3adf0a2c','port source hashes')
    need('def radix : ℕ := 2 ^ 47' in MASK.read_text() and 'def beta : ℕ := radix ^ 2011 - 1' in MASK.read_text() and '![beta, K, lowPort, highPort + beta]' in MASK.read_text() and 'CurrentMasks2011.ports (K : ℤ)' in KERNEL.read_text(),'port definitions')
    g=json.loads(GRAPH.read_bytes());rows=g['source'];need(g['witnesses']==list(VARS) and g['fixed_numerals']==list(PORTS) and len(rows)==84 and g['output']=='polynomial','graph signature');by={r[0]:r for r in rows};need(len(by)==84 and collections.Counter(r[1] for r in rows)=={'*':49,'+':18,'-':17},'operator counts')
    # Whole port values match the previously captured Lean evaluations.
    portreceipt=BASE/'reviews/equation14-historical-literal-binding/ports-receipt.json';need(sha(portreceipt)=='b9f356e64350b0d6c34d7dbd7b766561fbe3ec30374dd26158f92db92176f413','captured port receipt');captured=json.loads(portreceipt.read_bytes());need(captured['kernel_data_source_sha256']==sha(KERNEL),'port source match')
    sys.set_int_max_str_digits(0);binding=g['coefficient_binding'];whole={};records={}
    for i,name in enumerate(PORTS):
        e=binding['ports'][name];path=GRAPH.parent/binding['path']/e['file'];raw=gzip.decompress(path.read_bytes());record=captured['ports'][i];cp=BASE/'reviews/equation14-historical-literal-binding/port-outputs'/f'port{i}.txt.gz'
        need(sha(path)==e['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==e['raw_sha256']==record['integer_sha256'] and len(raw)==e['raw_bytes']==record['integer_bytes'],'payload '+name)
        need(sha(cp)==record['captured_gzip_sha256'] and int(gzip.decompress(cp.read_bytes()).strip())==int.from_bytes(raw,'big'),'captured '+name)
        whole[name]=int.from_bytes(raw,'big');records[name]=e['raw_sha256']
    need(whole['beta']==(1<<(47*2011))-1,'beta exact')
    # Construct a complete local N1 polynomial, including its cancellation.
    cache={n:symbol(n) for n in SYMS}
    def full(n):
        if type(n) is int:return const(n)
        if n not in cache:
            _,k,l,r=by[n];a,b=full(l),full(r);cache[n]=mul(a,b) if k=='*' else add(a,b,1 if k=='+' else -1)
        return cache[n]
    N1=full('N1');q=add(full('X'),mul(symbol('gamma'),full('H')))
    alt=add(add(mul(q,q),mul(const(2),mul(mul(full('a'),full('c')),q))),mul(full('H'),mul(full('c'),full('c'))),-1)
    need(N1==alt and deg(N1)==18,'main norm identity')
    # Store at least the three highest degree layers at each node. For a product,
    # omitted terms have degree at most three below its declared upper bound;
    # for a sum the same truncation remains safe. Sharpen when cancellation is
    # detected, and retain the certified 46-layer at correctedU.
    layers={n:(1 if n in VARS else 0,symbol(n)) for n in SYMS};events=[]
    for name,kind,l,r in rows:
        da,a=(0,const(l)) if type(l) is int else layers[l];db,b=(0,const(r)) if type(r) is int else layers[r]
        bound=da+db if kind=='*' else max(da,db);v=mul(a,b) if kind=='*' else add(a,b,1 if kind=='+' else -1);v={m:c for m,c in v.items() if sum(m[:13])>=bound-2}
        if name=='N1':bound=18;v={m:c for m,c in N1.items() if sum(m[:13])>=16};events.append(name)
        if name=='correctedU':need(bound==48 and deg(v)==46,'degree 48/47 cancellation');bound=46;v={m:c for m,c in v.items() if sum(m[:13])==46};events.append(name)
        if name=='sqU':v={m:c for m,c in v.items() if sum(m[:13])==92}
        need(v and deg(v)==bound,'unresolved high-degree cancellation '+name);layers[name]=(bound,v)
    need(events==['N1','correctedU'] and layers['polynomial'][0]==92,'exact symbolic degree bound')
    # Evaluate all actual fixed ports modulo the prime, independently of the
    # symbolic layer calculation; a nonzero t^92 coefficient is a lower bound.
    residues={n:whole[n]%P for n in PORTS}
    def diagonal(mutation=None):
        env={n:[0,1] for n in VARS};env.update({n:[v] for n,v in residues.items()})
        for name,k,l,r in rows:
            if mutation and name in mutation:k,l,r=mutation[name]
            env[name]=univ(env[l] if type(l) is str else [l%P],env[r] if type(r) is str else [r%P],k)
        return env['polynomial']
    out=diagonal();need(len(out)==93 and out[92]==557370225,'nonzero full-tuple diagonal coefficient')
    wrong=diagonal({'correctedU':('+','Na','correction')});need(len(wrong)==97,'sign mutation must restore degree 96')
    wrong2=diagonal({'sumPQ_U':('+','sqPQ','sqZ')});need(len(wrong2)<=81,'dropping corrected square lowers degree')
    live=set()
    def visit(n):
        if type(n) is int or n in live:return
        live.add(n)
        if n in by:visit(by[n][2]);visit(by[n][3])
    visit('polynomial');need(set(by)<=live and set(VARS)<=live and set(PORTS)<=live,'liveness')
    print(json.dumps({'status':'PASS_INDEPENDENT_2011_84_DEGREE_92','source_commit':'20c4dd9d3c','graph_sha256':sha(GRAPH),'operations':dict(sorted(collections.Counter(r[1] for r in rows).items())),'degree_upper_bound':92,'degree_drop_events':events,'modulus':P,'actual_port_residues':residues,'diagonal_t92_coefficient':out[92],'tuple_port_raw_sha256':records,'prior_port_receipt_sha256':sha(portreceipt),'negative_controls':['correction_sign_restores_degree_96','drop_corrected_square'],'scope':'External exact degree of the 84-row graph at the full actual 2011 tuple. No Lean expression binding, TeX semantics, iPRA endpoint or minimum claim.'},indent=2))
if __name__=='__main__':main()
