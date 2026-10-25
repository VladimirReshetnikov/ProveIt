#!/usr/bin/env python3
"""Independent interface audit for the combined arithmetic endpoints.

Checks the literal pre-normalization rows against the composition theorem;
uses no producer imports and makes no inference from sampled solutions.
"""
import json, hashlib, sys
from pathlib import Path
from collections import Counter
P=Path(__file__).resolve().parents[1]
endpoint=sys.argv[1] if len(sys.argv)>1 else 'natural242'
if endpoint not in ('natural242','integer378'):raise ValueError('select natural242 or integer378')
B=P/endpoint
RAW=B/('raw' if endpoint=='natural242' else 'natural_raw')
d=json.loads((RAW/'raw_audit_input.json').read_text())
cert=json.loads((RAW/'cap_certificate.json').read_text())

def req(cond,msg):
    if not cond: raise ValueError(msg)
def add(a,b):
    c=Counter(a);c.update(b);return {m:v for m,v in c.items() if v}
def neg(a):return {m:-v for m,v in a.items()}
def mul(a,b):
    c=Counter()
    for m,v in a.items():
        for n,w in b.items():c[tuple(sorted(m+n))]+=v*w
    return {m:v for m,v in c.items() if v}
def sc(a,k):return {m:k*v for m,v in a.items() if k*v}
def var(k):return {(k,):1}
def cn(k):return {():k} if k else {}
def sm(vals):
    out={}
    for v in vals:out=add(out,v)
    return out
rows=d['rows'];gates={int(k):rows[v] for k,v in d['gates'].items()}
labels={}
for r in rows:labels.setdefault(r['label'],[]).append(r)
nameids={v['name']:i for i,v in enumerate(d['variables'])}
def row(name):
    req(len(labels.get(name,[]))==1,'row absent or repeated '+name)
    return labels[name][0]
def expand_term(k,cut,memo):
    if k in cut or k not in gates:return var(k)
    if k in memo:return memo[k]
    r=gates[k]
    coeff=next((c for c,m in r['terms'] if m==[k]),None)
    req(coeff in (1,-1),'nonmonic definition')
    out={}
    for c,m in r['terms']:
        if m==[k]:continue
        req(k not in m,'cyclic definition')
        term=cn(-c//coeff)
        for j in m:term=mul(term,expand_term(j,cut,memo))
        out=add(out,term)
    memo[k]=out;return out
def exrow(r,cut):
    out={};memo={}
    for c,m in r['terms']:
        term=cn(c)
        for k in m:term=mul(term,expand_term(k,cut,memo))
        out=add(out,term)
    return out

def atom(a):
    req(a[0]=='v','nonvariable semantic atom');return a[1]
power_atoms={atom(p[k]) for p in d['powers'] for k in ('base','exponent','output')}
modular_atoms={atom(p['n']) for p in d['modular_requests']}
allatoms=power_atoms|modular_atoms
seeds={atom(p['exponent']):tuple(map(atom,p['pair'])) for p in d['seeds']}
required={atom(p['exponent']) for p in d['powers']}|modular_atoms
req(set(seeds)==required,'seed/request coverage mismatch')
req(set(seeds)<=allatoms,'seed omitted from frame')
req(cert==d['cap_certificate'],'cap certificate copies differ')
req({atom(a) for a in cert['frame']['all_atoms']}==allatoms,'wrong frame atom declaration')
W,A,Z=map(atom,d['scale']);L=atom(d['lower_A'])
req(max(allatoms)<W,'frame includes later private Pell data')
factor=cert['frame'].get('factor',1)
req(factor in (1,2),'unexpected frame factor')
req(exrow(row('shared.frame_definition'),allatoms|{W})==add(var(W),neg(sc(sm([cn(2)]+[var(a) for a in allatoms]),factor))),'actual frame row differs')
# Positive raw lower bounds; do not assume powers, factorials or binomials.
lower={i:0 for i in range(len(d['variables']))}
for k in sorted(gates):
    r=gates[k];coef=next((c for c,m in r['terms'] if m==[k]),None)
    req(coef in (1,-1),'gate not monic')
    rhs=[(-c//coef,m) for c,m in r['terms'] if m!=[k]]
    if all(c>=0 for c,m in rhs):
        total=0
        for c,m in rhs:
            for j in m:c*=lower[j]
            total+=c
        lower[k]=total
req(all(lower[k]>=1 for k in seeds),'a requested seed lacks raw positive definition')
req(lower[next(p['exponent'][1] for p in d['powers'])]>=16,'missing horizon floor')
# Separated lower frame: L^2 - ((W+1)^2-1)(WZ)^2 = 1, A=L+sigma.
frame=add(add(mul(var(L),var(L)),cn(-1)),neg(mul(add(mul(add(var(W),cn(1)),add(var(W),cn(1))),cn(-1)),mul(mul(var(W),var(Z)),mul(var(W),var(Z))))))
req(exrow(row('shared.last_norm_lower'),{W,L,Z})==frame,'lower frame norm differs')
slack=nameids['shared.A_slack']
req(expand_term(A,{L,slack},{})==add(var(L),var(slack)),'A not L plus natural slack')
xc,yc=map(atom,cert['cap']['pair']);u,v,bb=map(atom,cert['cap']['auxiliary']);ss,rr=map(atom,cert['cap']['comparison'])
for label,base,x,y in [('index_cap.norm1',A,xc,yc),('index_cap.norm2',A,u,v),('index_cap.norm3',bb,ss,rr)]:
    expected=add(add(add(mul(var(x),var(x)),mul(var(y),var(y))),neg(mul(mul(var(base),var(base)),mul(var(y),var(y))))),cn(-1))
    req(exrow(row(label),{base,x,y})==expected,'cap Pell norm differs '+label)
q4=nameids['index_cap.q4minus1'];vd=nameids['index_cap.Vquotient_minus1']
bq=nameids['index_cap.Bquotient'];sq=nameids['index_cap.Squotient'];rq=nameids['index_cap.Rquotient']
req(expand_term(bb,{yc,q4},{})==add(cn(1),mul(sc(var(yc),4),add(var(q4),cn(1)))),'cap B definition differs')
for label,cut,expected in [
 ('index_cap.V_positive_multiple',{v,yc,vd},add(var(v),neg(mul(mul(var(yc),var(yc)),add(var(vd),cn(1)))))),
 ('index_cap.B_mod_U',{bb,A,u,bq},add(var(bb),neg(add(var(A),mul(var(u),var(bq)))))),
 ('index_cap.S_mod_U',{ss,xc,u,sq},add(var(ss),neg(add(var(xc),mul(var(u),var(sq)))))),
 ('index_cap.R_mod_4Y',{rr,W,yc,rq},add(var(rr),neg(add(var(W),sc(mul(var(yc),var(rq)),4))))),
]:req(exrow(row(label),cut)==expected,'cap comparison differs '+label)
ys={y for x,y in seeds.values()}
z=atom(cert['residue']['quotient'])
errors={}
for k,(x,y) in seeds.items():
    errors=add(errors,mul(add(var(y),neg(var(k))),add(var(y),neg(var(k)))))
    if cert['residue'].get('recover_x',False):errors=add(errors,mul(add(var(x),cn(-1)),add(var(x),cn(-1))))
if factor==1:
    s=atom(cert['aggregate']['slack'])
    req({atom(a) for a in cert['aggregate']['ordinates']}==ys,'cap aggregate seed set differs')
    req(yc not in ys,'cap is its own principal seed')
    expected=add(var(yc),neg(sm([var(W),cn(1),var(s)]+[var(y) for y in ys])))
    req(exrow(row('index_cap.all_indices_bound'),ys|{W,yc,s})==expected,'literal aggregate differs')
    expected=sm([neg(mul(var(A),var(z))),var(z),errors])
    req(exrow(row('index_cap.squared_index_errors'),set(seeds)|ys|{A,z})==expected,'pooled error row differs')
else:
    req(cert['aggregate'] is None,'merged cap unexpectedly retains aggregate')
    req('index_cap.all_indices_bound' not in labels and 'index_cap.squared_index_errors' not in labels,'old cap row still present')
    expected=sm([var(yc),neg(var(W)),neg(errors),neg(mul(var(A),var(z))),var(z)])
    req(exrow(row('index_cap.merged_bound_errors'),set(seeds)|ys|{A,z,W,yc})==expected,'merged bound/error row differs')
for k,(x,y) in seeds.items():
    label=next(r['label'] for r in rows if r['label'].startswith('index') and r['label'].endswith('.norm1') and [1,[x,x]] in r['terms'])
    expected=add(add(add(mul(var(x),var(x)),mul(var(y),var(y))),neg(mul(mul(var(A),var(A)),mul(var(y),var(y))))),cn(-1))
    req(exrow(row(label),{A,x,y})==expected,'principal norm differs')
req(len(d['powers'])==6 and len(d['modular_requests'])==11 and len(seeds)==15 and not d['derivations'],'unexpected request inventory')
req(d['factorials'][0]['binomial']==d['product']['product']==d['binomials'][0]['output'],'factorial/product binomial split')
req(d['radix']['aggregate_count']==9,'CRT aggregate changed count')
req(d['amplification']['derived_label_sum'] not in [r[0] for r in d['ranges'][:9]],'derived label included in CRT aggregate')
# Hash bind the natural contraction endpoints; its algebraic checker is separately retained.
canonical=lambda x:json.dumps(x,sort_keys=True,separators=(',',':')).encode()
if endpoint=='natural242':
    c=json.loads((B/'natural/elimination_certificate.json').read_text())
    for filename,key in [('raw/equation.json','source_equation_sha256'),('natural/equation.json','target_equation_sha256')]:
        obj=json.loads((B/filename).read_text());req(hashlib.sha256(canonical(obj)).hexdigest()==c[key],'contraction hash mismatch '+filename)
    endpoint_hash=c['target_equation_sha256']
else:
    source=json.loads((B/'source.json').read_text());raw=json.loads((RAW/'equation.json').read_text())
    req(source['variables']==raw['variables'] and source['residuals']==raw['residuals'],'signed body differs from audited natural body')
    endpoint_hash=hashlib.sha256(canonical(raw)).hexdigest()
result={'status':'PASS','endpoint':endpoint,'frame_factor':factor,'merged_row':factor==2,'traces_certified':cert['residue'].get('recover_x',False),'checked_seed_norms':15,'exact_power_calls':6,'modular_calls':11,'all_requests_in_frame':True,'actual_frame_row':True,'actual_cap_rows':True,'actual_pooled_error_row':True,'all_seed_indices_positive_before_semantics':True,'minimum_raw_seed_lower_bound':min(lower[k] for k in seeds),'semantic_atoms_precede_private_frame':True,'audited_body_or_natural_endpoint_hash':endpoint_hash,'scope':'literal pre-normalization frame/cap/index composition and projection binding; inherited arithmetic/calculus calibration reviewed separately'}
(Path(__file__).resolve().parent/('INTERFACE_'+endpoint.upper()+'.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
