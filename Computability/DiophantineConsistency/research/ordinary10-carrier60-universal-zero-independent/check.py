from pathlib import Path
from hashlib import sha256
import json, sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary10-carrier60-universal-zero-independent')
for path,h in json.loads((D/'pins.json').read_text()).items():
    assert sha256(Path(path).read_bytes()).hexdigest()==h, path
g=json.loads(Path('research/ordinary10-carrier60-inverse-boundary/candidate.json').read_text())
assert g['fixed_numerals']==['beta','K0','MC','MF']
assert g['witnesses']==['n_J','n_F','n_C','n_w','n_s','n_h','n_tau','n_eta','n_zeta','n_gamma']
assert g['domain']=='nonnegative integers' and len(g['source'])==60
# Sparse integer polynomials in beta,K0,MC,MF; normalise all coefficients.
z=(0,0,0,0)
def cn(n): return {} if n==0 else {z:n}
def var(i):
    a=[0]*4;a[i]=1;return {tuple(a):1}
def add(a,b):
    d=a.copy()
    for k,v in b.items(): d[k]=d.get(k,0)+v
    return {k:v for k,v in d.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def mul(a,b):
    d={}
    for i,x in a.items():
        for j,y in b.items():
            k=tuple(u+v for u,v in zip(i,j));d[k]=d.get(k,0)+x*y
    return {k:v for k,v in d.items() if v}
def atom(x):return cn(x) if isinstance(x,int) else vals[x]
vals={name:var(i) for i,name in enumerate(g['fixed_numerals'])}
vals.update({'n_J':cn(0),'n_F':var(1),'n_C':cn(0),'n_w':cn(1),
             'n_s':cn(0),'n_h':cn(0),'n_tau':cn(3363),'n_eta':cn(1527),
             'n_zeta':cn(850),'n_gamma':cn(292)})
for name,op,a,b in g['source']:
    assert name not in vals and op in '+-*'
    a,b=atom(a),atom(b)
    vals[name]=add(a,b) if op=='+' else add(a,neg(b)) if op=='-' else mul(a,b)
for name,n in {'q':1,'X':1,'Y':1,'U':1,'C':1,'k':2378,'c':3905,
               'a':2,'H':11,'Delta':15,'ell':2378,'R':0,'Dstar':-15124,
               'Bres':0,'firstres':0,'A1':0,'out':0}.items():
    assert vals[name]==cn(n),(name,vals[name],n)
assert vals['qF']==neg(var(1))
assert add(vals['qF'],neg(vals['C']))==add(neg(var(1)),cn(-1))
assert 3363**2==1+2*2378**2
assert 15124**2==1+15*3905**2
# Check literal topological dependencies and full liveness separately.
rows={};leaves=set(g['fixed_numerals']+g['witnesses'])
for name,op,a,b in g['source']:
    assert name not in rows and name not in leaves
    assert all(isinstance(x,int) or x in leaves or x in rows for x in (a,b))
    rows[name]=(a,b)
live=set()
def visit(x):
    if isinstance(x,int) or x not in rows or x in live:return
    live.add(x)
    for y in rows[x]:visit(y)
visit(g['output']);assert len(live)==60
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'symbolic_port_variables':g['fixed_numerals'],'live_literal_operations':len(live),
 'all_port_polynomial_output_zero':True,'all_witnesses_natural_for_natural_ports':True,
 'old_alpha':'-K0-1','fixed_compact_tuple_included':True,
 'old_graph_existence_or_nonequivalence_proved':False,'lean_executed':False},indent=2,sort_keys=True))
