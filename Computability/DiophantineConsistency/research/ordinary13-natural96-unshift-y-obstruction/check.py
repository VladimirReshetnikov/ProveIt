#!/usr/bin/env python3
"""Evaluate the C-fold Y=0 obstruction at toy and authenticated ports."""
from pathlib import Path
import gzip,hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
def digest(x):return hashlib.sha256(x).hexdigest()
def load(path,sha):
 b=path.read_bytes();assert digest(b)==sha,str(path);return json.loads(b)
a=load(D/'research/ordinary13-natural-cfold97-degree28/candidate.json','8c56deec58c4fbe29ab024fc5a61628ec0d677858c9bc6eb066b4f81244ee2e6')
b=load(P/'candidate.json','076e538c34bc2ace133856e7b6ab3a94e885668e381a96ecc48ca92ea8250419')
assert ['Y','+','n_Y',1] in a['source']
assert b['source']==[[n,op,'n_Y' if x=='Y' else x,'n_Y' if y=='Y' else y] for n,op,x,y in a['source'] if n!='Y']
assert len(b['source'])==b['operations']==96
assert b['parent_sha256']==digest((D/'research/ordinary13-natural-cfold97-degree28/candidate.json').read_bytes())
def calc(g,v):
 e=v.copy()
 for n,op,x,y in g['source']:
  x=x if type(x) is int else e[x];y=y if type(y) is int else e[y]
  e[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return e
def witness(beta,K0,MC,MF):
 assert beta>=2 and K0>=1 and MC>0 and MF>0
 q=beta+1;X=(1-K0)%beta or beta
 R=(beta-1+beta*beta)*(q*q-1)+MC+MF*q
 B=X+q*(K0-1)
 assert R>0 and B>0 and B%beta==0
 r=B//beta+1
 v={'n_J':1,'n_F':0,'n_alpha':beta-2,'n_f':2,'n_i':2,'n_T':R-1,
    'n_X':X-1,'n_Y':0,'n_r':r,'n_eta':0,'n_zeta':R-1,'n_u':1,'n_gamma':0,
    'beta':beta,'K0':K0,'MC':MC,'MF':MF}
 assert all(v[n]>=0 for n in b['witnesses'])
 e=calc(b,v)
 for n,x in {'qm':beta,'q':q,'X':X,'U':0,'ell':0,'c':1,
             'k':R+1,'R':R,'Bt':B,'Z':q**3*beta,'Dstar':0,'Q':9,'V':-1,
             'A0':0,'A1':0,'Fa':1,'g72':0,'out':0}.items():assert e[n]==x,n
 return v
toy=witness(2,1,1,1)
assert toy=={'n_J':1,'n_F':0,'n_alpha':0,'n_f':2,'n_i':2,'n_T':43,
             'n_X':1,'n_Y':0,'n_r':2,'n_eta':0,'n_zeta':43,'n_u':1,'n_gamma':0,
             'beta':2,'K0':1,'MC':1,'MF':1}
assert calc(a,toy)['out']!=0
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
bind=load(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b115=load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
ports={}
for n,m in bind['ports'].items():
 assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip']
 z=(p72/m['path']).read_bytes();assert digest(z)==m['sha256_gzip']
 raw=gzip.decompress(z);assert len(raw)==m['raw_bytes'] and digest(raw)==m['sha256_raw']
 ports[n]=int.from_bytes(raw,'little')
assert set(ports)=={'beta','K0','MC','MF'}
witness(**ports)
print(json.dumps({'scope':'counterexample to forced Y positivity and unchanged-coordinate transfer only',
                  'variables':13,'unshifted_gates':96,'toy_zero':True,
                  'same_toy_coordinates_parent_nonzero':True,'authenticated_ports_zero':True,
                  'no_global_existence_or_lean_claim':True},sort_keys=True,indent=2))
