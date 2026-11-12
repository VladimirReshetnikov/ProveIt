#!/usr/bin/env python3
"""Independent exact polynomial and compact port verification; no Lean."""
import gzip, hashlib, json, sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(path,digest):
 data=(D/path).read_bytes(); assert hashlib.sha256(data).hexdigest()==digest,path; return data
parent=json.loads(pin('research/ordinary13-natural-residue-forced89-degree56/candidate.json','c18892fc5e50e091411cf24511481995ad2fdbab20e55068787722feca41a22a'))
probe=json.loads(pin('research/ordinary13-residue89-unshift-s-full-zero/probe.json','442ec99590e23393a619980686e5578f611c55b9feedb2acec6c8958fbfa54e4'))
pin('reviews/ordinary13-natural-residue-forced89-independent/result.json','17b5fcebce8f734b68124b7ecfa477fec1f00ac73cadda915c29128fc27b1df8')
assert parent['domain']=='nonnegative integers' and probe['witnesses']==parent['witnesses'] and probe['fixed_numerals']==parent['fixed_numerals'] and probe['output']==parent['output']
replace=lambda x:'n_s' if x=='shift_s' else x
assert probe['source']==[[n,op,replace(a),replace(b)] for n,op,a,b in parent['source'] if n!='shift_s'] and len(probe['source'])==88
# Sparse integer polynomial ring in (beta,K0,MC,MF,h); coefficients are exact.
zero=(0,)*5
def const(n): return {zero:n} if n else {}
def var(i): return {tuple(int(i==j) for j in range(5)):1}
def plus(a,b,sign=1):
 z=a.copy()
 for m,c in b.items(): z[m]=z.get(m,0)+sign*c
 return {m:c for m,c in z.items() if c}
def times(a,b):
 z={}
 for ma,ca in a.items():
  for mb,cb in b.items():
   m=tuple(x+y for x,y in zip(ma,mb));z[m]=z.get(m,0)+ca*cb
 return {m:c for m,c in z.items() if c}
b,K,M,N,h=map(var,range(5));one=const(1);q=plus(b,one);q2=times(q,q)
X=plus(plus(times(b,h),K,-1),one,-1)
R=plus(times(plus(one,times(b,b)),plus(q2,one,-1)),plus(M,times(q,N)))
t=plus(times(plus(b,one,-1),h),one,-1);P=times(b,t);k=plus(R,one)
r=plus(plus(times(k,plus(P,one,-1)),t),one)
e={'beta':b,'K0':K,'MC':M,'MF':N,'n_J':one,'n_F':{},'n_alpha':{},'n_f':const(2),'n_i':const(2),'n_T':plus(R,one,-1),'n_X':X,'n_s':{},'n_r':r,'n_eta':{},'n_zeta':plus(R,one,-1),'n_y':one,'n_gamma':{}}
for name,op,a,c in probe['source']:
 a=const(a) if isinstance(a,int) else e[a];c=const(c) if isinstance(c,int) else e[c]
 e[name]=times(a,c) if op=='*' else plus(a,c,-1 if op=='-' else 1)
for name in ['A0','A1','g72','Fam','out']: assert e[name]=={},name
assert e['Bt']==P and e['R']==R and e['Y']=={} and e['V']==const(-1)
root='con-zfc-diophantine-forms/72-congruence-sextic/positive13/'
p72=json.loads(pin(root+'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
p115=json.loads(pin('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
ports={}
for name,meta in p72['ports'].items():
 assert all(meta[x]==p115['ports'][name][x] for x in ['sha256_raw','sha256_gzip'])
 raw=gzip.decompress(pin(root+meta['path'],meta['sha256_gzip']))
 assert len(raw)==meta['raw_bytes'] and hashlib.sha256(raw).hexdigest()==meta['sha256_raw']
 ports[name]=int.from_bytes(raw,'little')
beta,K0,MC,MF=(ports[x] for x in ('beta','K0','MC','MF'))
assert beta>=3 and min(K0,MC,MF)>=0
h0=(K0+beta+1)//beta;X0=beta*h0-K0-1;t0=(beta-1)*h0-1
assert h0>=1 and X0>=1 and t0>=1
# R, r and all remaining coordinates are natural by their positive-factor formulas;
# the exact polynomial identity above applies at these concrete parameter values.
print(json.dumps({'scope':'exact full graph identity and authenticated compact witness hypotheses; no Lean or global zero-existence comparison','operations':88,'all_four_residuals_identically_zero':True,'compact_ports_authenticated':True,'compact_witness_natural':True,'unshifted_s_equals_zero':True,'lean_elaborated':False},sort_keys=True,indent=2))
