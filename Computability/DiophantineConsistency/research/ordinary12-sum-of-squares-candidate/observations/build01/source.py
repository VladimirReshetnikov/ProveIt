#!/usr/bin/env python3
"""Construct the five-gate residual-square candidate and degree evidence."""
from pathlib import Path
from hashlib import sha256
import gzip, json
D = Path(__file__).resolve().parents[2]
S = D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement'
G = S/'circuits/positive12_95_degree70.json'
PIN='2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22'
BIND='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'
def insist(ok, msg):
    if not ok: raise RuntimeError(msg)
raw=G.read_bytes();insist(sha256(raw).hexdigest()==PIN,'parent graph drift')
g=json.loads(raw); rows=g['source']
insist(len(rows)==95 and rows[-6:]==[['g94','+',1,'A0'],['g95','+',1,'A1'],['g96','*','g94','g95'],['g97','+',1,'N'],['g98','*','g96','g97'],['P12','-','g98',1]],'parent tail drift')
tail=[['A0sq','*','A0','A0'],['A1sq','*','A1','A1'],['Nsq','*','N','N'],['sum01','+','A0sq','A1sq'],['P12','+','sum01','Nsq']]
newrows=rows[:-6]+tail
known=set(g['witnesses']+g['fixed_numerals'])|set(range(5))
for name,op,a,b in newrows:
    insist(name not in known and a in known and b in known and op in '+-*','bad graph topology')
    known.add(name)
parents={name:(a,b) for name,op,a,b in newrows};live=set();todo=['P12']
while todo:
    v=todo.pop()
    if v in parents and v not in live: live.add(v);todo.extend(parents[v])
insist(len(newrows)==len(live)==94,'nonlive or wrong count')
deg={n:1 for n in g['witnesses']};deg.update({n:0 for n in g['fixed_numerals']});deg.update({n:0 for n in range(5)})
for n,op,a,b in newrows:deg[n]=deg[a]+deg[b] if op=='*' else max(deg[a],deg[b])
# Exact ring identity: h = (V+n)^2-1-Q*n*(2*V+n).
# Check both expressions as polynomials in independent Q,V,n over Z.
def padd(a,b):
    z=a.copy()
    for k,v in b.items(): z[k]=z.get(k,0)+v
    return {k:v for k,v in z.items() if v}
def pneg(a):return {k:-v for k,v in a.items()}
def pmul(a,b):
    z={}
    for ka,va in a.items():
        for kb,vb in b.items():
            k=tuple(x+y for x,y in zip(ka,kb));z[k]=z.get(k,0)+va*vb
    return {k:v for k,v in z.items() if v}
one={(0,0,0):1};Q={(1,0,0):1};V={(0,1,0):1};n={(0,0,1):1}
vplus=padd(V,n)
lhs=padd(pmul(padd(one,pneg(Q)),pmul(vplus,vplus)),padd(pmul(Q,pmul(V,V)),pneg(one)))
rhs=padd(padd(pmul(vplus,vplus),pneg(one)),pneg(pmul(pmul(Q,n),padd(padd(V,V),n))))
insist(lhs==rhs,'h polynomial identity failed')
# Replay all degree bounds with the justified 13 bound at h. The source
# shape is pinned by the complete parent hash and checked explicitly here.
lookup={r[0]:r[1:] for r in newrows}
insist(all(lookup[k]==v for k,v in {'vn':['+','V','n'],'vn2':['*','vn','vn'],
 'polarV2':['*','V','V'],'polarQV2':['*','Q','polarV2'],
 'polarCy':['-','polarQV2',1],'oneQ':['-',1,'Q'],
 'polarHpart':['*','oneQ','vn2'],'h':['+','polarHpart','polarCy']}.items()),'h graph shape')
tight={n:1 for n in g['witnesses']};tight.update({n:0 for n in g['fixed_numerals']});tight.update({n:0 for n in range(5)})
for n,op,a,b in newrows:
    tight[n]=tight[a]+tight[b] if op=='*' else max(tight[a],tight[b])
    if n=='h':
        # deg Q <= 6, V <= 6, n <= 1; the verified identity gives 13.
        insist(tight['Q']<=6 and tight['V']<=6 and tight['n']==1,'h degree premises')
        tight[n]=max(2*max(tight['V'],tight['n']), tight['Q']+tight['n']+max(tight['V'],tight['n']))
insist(tight['P12']==84,'unexpected tightened upper bound')
# A nonzero coefficient after reducing actual retained fixed ports modulo p
# proves an integer degree lower bound. We use a univariate linear substitution.
braw=(S/'coefficients/BINDING.json').read_bytes();insist(sha256(braw).hexdigest()==BIND,'binding drift')
b=json.loads(braw);prime=1_000_000_007
values={n:[0,i+2] for i,n in enumerate(g['witnesses'])};values.update({n:[n] for n in range(5)})
for name in g['fixed_numerals']:
    meta=b['ports'][name];z=(S/'coefficients'/meta['file']).read_bytes()
    insist(sha256(z).hexdigest()==meta['sha256_gzip'],'gzip drift '+name)
    x=gzip.decompress(z);insist(sha256(x).hexdigest()==meta['sha256_raw'] and len(x)==meta['raw_bytes'],'raw drift '+name)
    values[name]=[int.from_bytes(x,'little')%prime]
def calc(op,a,b):
    if op=='*':
        z=[0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
    else:
        z=[((a[i] if i<len(a) else 0)+(1 if op=='+' else -1)*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))]
    while len(z)>1 and z[-1]==0:z.pop()
    return z
for name,op,a,b in newrows:values[name]=calc(op,values[a],values[b])
insist(len(values['P12'])-1==tight['P12'] and values['P12'][-1]!=0,'degree witness failed')
graph={'name':'positive12_94_sum_squares_candidate','domain':g['domain'],
       'witnesses':g['witnesses'],'fixed_numerals':g['fixed_numerals'],
       'output':'P12','operations':len(newrows),
       'operation_breakdown':{op:sum(r[1]==op for r in newrows) for op in ['*','+','-']},
       'syntactic_degree_upper_bound':deg['P12'],'externally_checked_exact_degree':tight['P12'],'residuals':['A0','A1','N'],
       'parent_graph_sha256':PIN,'coefficient_binding_sha256':BIND,'source':newrows}
out=Path(__file__).with_name('candidate.json')
out.write_text(json.dumps(graph,indent=2)+'\n')
print(json.dumps({'graph_sha256':sha256(out.read_bytes()).hexdigest(),'operations':len(newrows),
                  'live_operations':len(live),'operation_breakdown':graph['operation_breakdown'],
                  'syntactic_degrees':{n:deg[n] for n in ['A0','A1','N','P12']},
                  'tight_degrees_upper':{n:tight[n] for n in ['Q','V','h','den','polarT','polarA','polarCorrection','N','P12']},
                  'substitution':'witness i maps to (i+2)*t', 'prime':prime,
                  'substitution_degree':len(values['P12'])-1,
                  'substitution_leading_coefficient_mod_prime':values['P12'][-1],
                  'residual_degrees_mod_prime':{n:len(values[n])-1 for n in ['A0','A1','N']},
                  'fixed_port_residues':{n:values[n][0] for n in g['fixed_numerals']}},indent=2,sort_keys=True))
