#!/usr/bin/env python3
"""Separate reviewer check: imports no construction builder or verifier.

Usage: python3 p13_independent_check.py [path/to/positive13]
"""
from collections import Counter
from pathlib import Path
import gzip, hashlib, json, sys

ROOT=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent
def check(ok,why):
    if not ok:raise ValueError(why)

def add(a,b,sign=1):
    out=dict(a)
    for m,c in b.items():
        out[m]=out.get(m,0)+sign*c
        if not out[m]:del out[m]
    return out

def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            key=tuple(x+y for x,y in zip(m,n))
            out[key]=out.get(key,0)+c*d
    return {m:c for m,c in out.items() if c}

def scale(a,c):return {m:c*v for m,v in a.items() if c*v}
def power(a,n):
    out=literal(1)
    for _ in range(n):out=mul(out,a)
    return out

packet=json.loads((ROOT/'polynomial.json').read_text())
witnesses=packet['witnesses'];ports=packet['fixed_numerals'];names=witnesses+ports
check(len(witnesses)==13 and len(ports)==4,'Dimensions')
zero=(0,)*len(names)
def literal(n):return {zero:n} if n else {}
symbols={name:{tuple(int(i==j) for i in range(len(names))):1} for j,name in enumerate(names)}
def degree(poly):return max((sum(m[:13]) for m in poly),default=-1)
def head(poly):
    d=degree(poly)
    return d,{m:c for m,c in poly.items() if sum(m[:13])==d}
records={};complete=dict(symbols);leading={n:head(p) for n,p in symbols.items()}
fallback=[]
def full(name):
    if type(name) is int:return literal(name)
    if name not in complete:
        op,a,b=records[name]
        complete[name]=mul(full(a),full(b)) if op=='*' else add(full(a),full(b),-1 if op=='-' else 1)
    return complete[name]
def ld(name):return head(literal(name)) if type(name) is int else leading[name]
for name,op,a,b in packet['source']:
    check(name not in leading and op in ('+','-','*'),'Unique binary register')
    check(all(type(z) is int or z in leading for z in (a,b)),'Topological source')
    records[name]=(op,a,b);da,pa=ld(a);db,pb=ld(b)
    if op=='*':
        poly=mul(pa,pb);result=(da+db,poly) if poly else (-1,{})
    elif da>db:result=(da,pa)
    elif db>da:result=(db,pb if op=='+' else scale(pb,-1))
    else:
        poly=add(pa,pb,-1 if op=='-' else 1)
        if poly:result=(da,poly)
        else:
            result=head(full(name));fallback.append({'register':name,'terms':len(full(name)),'degree':result[0]})
    leading[name]=result

# An independently written homogeneous form, not a sampled ray, proves
# the precise top degree before any specialization of the fixed tuple.
q0=mul(symbols['beta'],symbols['J'])
E0=mul(mul(symbols['w'],symbols['s']),power(q0,4))
c0=mul(mul(add(symbols['eta'],symbols['zeta']),symbols['s']),power(q0,3))
nt0=add(mul(symbols['w'],add(add(q0,symbols['F'],-1),symbols['alpha'],-1)),mul(symbols['z'],q0),-1)
expected=scale(mul(mul(mul(mul(mul(mul(mul(power(q0,8),power(E0,8)),power(c0,9)),symbols['gamma']),power(symbols['i'],2)),power(symbols['T'],2)),power(symbols['f'],6)),nt0),-512)
check(leading[packet['output']]==(114,expected),'Exact full homogeneous form')
check({n:leading[n][0] for n in ('Nmain','Ns','N','Nt','delta')}=={'Nmain':26,'Ns':22,'N':64,'Nt':2,'delta':12},'Component degrees')
diagonal={}
for m,c in expected.items():
    key=m[13:];diagonal[key]=diagonal.get(key,0)+c
diagonal={m:c for m,c in diagonal.items() if c}
check(diagonal=={(67,0,0,0):2**19},'Actual-slice nonzero diagonal leader')

# Direct four-indeterminate norm identity.
d,x,A,e=[symbols[n] for n in witnesses[:4]]
lhs=add(power(add(mul(d,add(power(x,2),A,-1)),e,-1),2),scale(mul(mul(d,A),e),4),-1)
rhs=add(power(add(mul(d,add(power(x,2),A)),e,-1),2),scale(mul(mul(power(d,2),power(x,2)),A),4),-1)
check(lhs==rhs,'Centered norm identity')

cost=Counter(op for _,op,_,_ in packet['source'])
check(cost=={'+':19,'-':18,'*':46},'Operation count')
live={packet['output']}
for name,op,a,b in reversed(packet['source']):
    check(name in live,'Dead register')
    live.update(z for z in (a,b) if isinstance(z,str))
check(set(names)<=live,'Unused formal input')

binding=json.loads((ROOT/'COEFFICIENT_BINDING.json').read_text());actual={}
for item in binding['payloads']:
    compressed=(ROOT/item['path']).read_bytes();raw=gzip.decompress(compressed)
    check(hashlib.sha256(raw).hexdigest()==item['sha256'],'Raw coefficient hash')
    check(hashlib.sha256(compressed).hexdigest()==item['gzip_sha256'],'Compressed coefficient hash')
    check(len(raw)==item['bytes'],'Coefficient size')
    actual[item['port']]=int.from_bytes(raw,'little')
    check(actual[item['port']].bit_length()==item['bits'],'Coefficient bit count')
beta=actual['beta'];native_mf=actual['MF_source']-beta;mc=actual['MC']
check(beta==(1<<590069)-1 and actual['K']>0,'Native base and transport coefficient')
check(0<mc<beta and 0<native_mf<beta,'Native mask range')
check(mc%4==2 and native_mf%8==4,'Native low residues')
check(mc.bit_count()+native_mf.bit_count()==590069,'Exact native population')
check(binding['port_aliases']=={'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'},'Whole-tuple aliases')
pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
for pin in pins:
    raw=(ROOT/pin['local_path']).read_bytes()
    check(len(raw)==pin['byte_size'] and hashlib.sha256(raw).hexdigest()==pin['sha256'],'Source pin bytes/hash')
    if pin.get('git_blob_sha1'):
        check(hashlib.sha1(('blob '+str(len(raw))+'\0').encode()+raw).hexdigest()==pin['git_blob_sha1'],'Git blob hash')

receipt={'status':'PASS','constructor_imports':False,'witnesses':13,'gates':dict(cost),'exact_degree':114,
         'exact_top_form':'-512*q0^8*E0^8*c0^9*gamma*i^2*T^2*f^6*Nt2',
         'diagonal_top':'2^19*beta^67','exact_cancellation_fallbacks':fallback,
         'native_mask_invariants':True,'pinned_files':len(pins),
         'polynomial_sha256':hashlib.sha256((ROOT/'polynomial.json').read_bytes()).hexdigest(),
         'scope':'Independent finite algebra, exact coefficient invariants, counts and provenance; semantic review is P13_REVIEW.md.'}
out=ROOT/'REVIEW_CHECKS.json'
out.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
