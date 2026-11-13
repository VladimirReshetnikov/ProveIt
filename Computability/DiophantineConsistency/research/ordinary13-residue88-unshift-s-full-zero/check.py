#!/usr/bin/env python3
"""Check an exact symbolic full-zero family and compact bytes; no Lean."""
from pathlib import Path
import gzip,hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
pr=pin(D/'research/ordinary13-natural-residue-forced88-degree60/candidate.json','cb488cb849c08c11d159f8805fdd7664c6472cbd41cefadc530e21060a5a1dd2');p=json.loads(pr)
z=json.loads(pin(P/'probe.json','e69412ac7650ba5de4bde6dbbf5e1904259b4fbb674b896b6f576f288d629e55'))
sub=lambda x:'n_s' if x=='shift_s' else x
assert z['parent_sha256']==sha(pr) and z['witnesses']==p['witnesses'] and z['fixed_numerals']==p['fixed_numerals'] and z['output']==p['output']
assert z['source']==[[n,o,sub(a),sub(b)] for n,o,a,b in p['source'] if n!='shift_s'] and len(z['source'])==87
# Exact sparse integer polynomial evaluation of the whole modified graph.
def con(x):return {():x} if x else {}
def var(x):return {(x,):1}
def add(a,b,s=1):
 z=dict(a)
 for m,v in b.items():z[m]=z.get(m,0)+s*v
 return {m:v for m,v in z.items() if v}
def mul(a,b):
 z={}
 for x,v in a.items():
  for y,w in b.items():
   m=tuple(sorted(x+y));z[m]=z.get(m,0)+v*w
 return {m:v for m,v in z.items() if v}
b,K,L,H,h=map(var,['beta','K0','MC','MF','h']);q=add(b,con(1));q2=mul(q,q)
w=add(add(mul(b,h),K,-1),con(1),-1);X=mul(q,w);R=add(mul(add(con(1),mul(b,b)),add(q2,con(1),-1)),add(L,mul(q,H)))
k=add(R,con(1));t=add(mul(add(b,con(1),-1),add(w,h)),con(1),-1);transport=mul(b,t)
r=add(add(mul(k,add(transport,con(1),-1)),t),con(1))
env={'beta':b,'K0':K,'MC':L,'MF':H,'n_J':con(1),'n_F':con(0),'n_alpha':con(0),'n_f':con(2),'n_i':con(2),'n_T':add(R,con(1),-1),'n_w':w,'n_s':con(0),'n_r':r,'n_eta':con(0),'n_zeta':add(R,con(1),-1),'n_y':con(1),'n_gamma':con(0)}
for n,o,a,c0 in z['source']:
 a=con(a) if type(a) is int else env[a];c0=con(c0) if type(c0) is int else env[c0]
 env[n]=mul(a,c0) if o=='*' else add(a,c0,1 if o=='+' else -1)
assert env['R']==R and env['Bt']==transport and env['k']==k and env['Y']=={} and env['U']=={}
assert env['Q']==con(9) and env['V']==con(-1) and env['Fa']==con(1)
assert all(env[n]=={} for n in ('A0','A1','g72','Fam','out'))
# Compact port bytes and actual finite witness; values are never decimal-printed.
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
binding=json.loads(pin(root/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
b115=json.loads(pin(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
ports={}
for n,meta in binding['ports'].items():
 assert b115['ports'][n]['sha256_raw']==meta['sha256_raw'] and b115['ports'][n]['sha256_gzip']==meta['sha256_gzip']
 raw=gzip.decompress(pin(root/meta['path'],meta['sha256_gzip']));assert len(raw)==meta['raw_bytes'] and sha(raw)==meta['sha256_raw']
 ports[n]=int.from_bytes(raw,'little')
assert ports['beta']>=3 and all(ports[n]>=0 for n in ('K0','MC','MF'))
def witness(port):
 beta,K0,MC,MF=(port[n] for n in ('beta','K0','MC','MF'));assert beta>=3 and min(K0,MC,MF)>=0
 h=(K0+2+beta-1)//beta;w=beta*h-K0-1;assert w>=1;X=(beta+1)*w
 q=beta+1;R=(1+beta*beta)*(q*q-1)+MC+q*MF;assert R>0
 t=(beta-1)*(w+h)-1;assert t>=1;B=beta*t;k=R+1;r=k*(B-1)+t+1
 return {'n_J':1,'n_F':0,'n_alpha':0,'n_f':2,'n_i':2,'n_T':R-1,'n_w':w,'n_s':0,'n_r':r,'n_eta':0,'n_zeta':R-1,'n_y':1,'n_gamma':0}
def calc(g,port,v):
 e={**port,**v}
 for n,o,a,b in g['source']:
  a=a if type(a) is int else e[a];b=b if type(b) is int else e[b]
  e[n]=a*b if o=='*' else a+b if o=='+' else a-b
 return e
# The toy instance also witnesses failure of unchanged-coordinate transfer.
toy={'beta':3,'K0':0,'MC':0,'MF':0};v=witness(toy);e=calc(z,toy,v);ep=calc(p,toy,v)
assert all(x>=0 for x in v.values()) and e['out']==0 and ep['out']!=0
# For compact ports the all-graph identity above is exact; check the instantiated
# arithmetic using residue-level equalities, avoiding giant unused gate outputs.
v=witness(ports);beta=ports['beta'];K0=ports['K0'];X=(beta+1)*v['n_w'];R=v['n_T']+1;P0=(beta-1)*(X+K0)-1;t0=P0//beta
assert all(x>=0 for x in v.values()) and v['n_s']==0 and P0>0 and P0%beta==0
assert v['n_r']==(R+1)*(P0-1)+t0+1
print(json.dumps({'scope':'exact polynomial full-zero family and compact-port instance; no global zero-existence or iPRA conclusion','probe_operations':87,'symbolic_full_output_zero':True,'toy_full_zero':True,'toy_same_vector_parent_nonzero':True,'compact_full_zero_by_exact_family':True,'compact_R_bits':R.bit_length(),'compact_X_bits':X.bit_length(),'compact_r_bits':v['n_r'].bit_length(),'lean_elaboration':False},sort_keys=True,indent=2))
