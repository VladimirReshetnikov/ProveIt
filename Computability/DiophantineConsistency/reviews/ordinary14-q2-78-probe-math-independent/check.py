#!/usr/bin/env python3
"""Independent graph, port, recurrence and ray controls; no Lean."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,json,subprocess,sys
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-q2-78-probe';P=D/'research/ordinary14-direct-pell79'
def sha(x):return hashlib.sha256(x.read_bytes()).hexdigest()
assert sha(A/'candidate.json')=='9572564c9184110722bbd94cc928a224b48cedc935f3bdc59dea30b603ad7710'
assert sha(P/'candidate.json')=='5c5e2c089d0f10450374219e9d74883235fd0ef3b10d31d6df09a7dc498e2507'
readme=(A/'README.md').read_bytes()
tail=b'\nIndependent mathematical review is recorded in\n`../../reviews/ordinary14-q2-78-probe-math-independent/`.\n'
assert hashlib.sha256(readme).hexdigest()=='2d9b3698a09286ff18a38e326a984117317a3cb61f5c4e895402bb586040bd3e' and readme.endswith(tail)
assert hashlib.sha256(readme[:-len(tail)]).hexdigest()=='566bd4ba47b7fa388e215b879ee973fd22bbf98331299077b1e30050213980d7'
c=json.loads((A/'candidate.json').read_bytes());p=json.loads((P/'candidate.json').read_bytes());assert len(c['source'])==78 and len(p['source'])==79
assert c['witnesses']==p['witnesses'] and c['fixed_numerals']==p['fixed_numerals']
expected=[]
for row in p['source']:
 if row[0]=='q3':assert row==['q3','*','q','q2'];continue
 if row[0]=='Y':assert row==['Y','*','q3','s'];expected.append(['Y','*','q2','s'])
 else:expected.append(row)
assert c['source']==expected and c['output']==p['output']
seen=set(c['witnesses']+c['fixed_numerals']);live={c['output']}
for name,op,a,b in c['source']:
 assert name not in seen and op in '+-*' and all(isinstance(t,int) or t in seen for t in (a,b));seen.add(name)
for name,op,a,b in reversed(c['source']):
 if name in live:live.update(x for x in (a,b) if isinstance(x,str))
assert all(row[0] in live for row in c['source']) and set(c['witnesses']+c['fixed_numerals'])<=live
for name,digest in {
 'reviews/current14-carrier64-current-full-zero-independent/README.md':'517414af485e9505406c11227ad4e908f5cdcdb363d2e77f2385dbcaccd92b14',
 'reviews/ordinary13-folded-root86-toy-full-zero-independent/README.md':'cdb3ac6f1c8ced3f868222026dbededdb2cea67e6b9859a833a26f08561c784f',
 'reviews/current14-carrier64-pell-floor-independent/README.md':'4c79d65d6dea64a443c73205d8b678f6da75ee0042f124e161fd81da5da6f253'}.items():assert sha(D/name)==digest
# Independent exact small Pell completion controls, not the actual huge witness.
for a in (1,2,3):
 A0=a+2; Delta=A0*A0-1;d,c0=1,0
 for _ in range(3):d,c0=A0*d+Delta*c0,d+A0*c0
 f,L=1,0
 for _ in range(c0):f,L=f*d+Delta*L*c0,f*c0+L*d
 assert L%(c0*c0)==0
 S=Delta*L;xx,yy=1,0
 for _ in range(3):xx,yy=S*xx+(S*S-1)*yy,xx+S*yy
 assert xx%S==0
 V=xx//S
 assert (V+c0)%(f*f)==0 and (V+3)%c0==0
 T,rem=divmod(V+c0+f*f*3,c0*f*f)
 assert rem==0 and T>0 and yy>V
 Q=Delta*(f*f-1);I=(Delta*L//(c0*c0))*c0*c0
 assert Q==I*I and yy*yy-Q*(yy*yy-V*V)==1
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';B=json.loads((root/'ACTIVE_BINDING.json').read_bytes());Q=json.loads((D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json').read_bytes());ports={}
for name,t in B['ports'].items():
 z=(root/t['path']).read_bytes();raw=gzip.decompress(z)
 assert hashlib.sha256(z).hexdigest()==t['sha256_gzip']==Q['ports'][name]['sha256_gzip']
 assert hashlib.sha256(raw).hexdigest()==t['sha256_raw']==Q['ports'][name]['sha256_raw'] and len(raw)==t['raw_bytes']
 ports[name]=int.from_bytes(raw,'little')
assert ports['beta']==2**590069-1
assert ports['beta']>=46 and ports['K0']>=0 and 0<ports['MC']<ports['beta'] and 0<ports['MF']<2*ports['beta']
B=590069;beta=ports['beta'];q=beta+1;e=439547
F=(ports['K0']+2**e)%beta;alpha=beta-F
assert 0<F<beta and q-F-alpha==1
G=beta*(q-F)+alpha;R=G*(q*q-1)+ports['MC']+q*ports['MF'];N=(R-1)//2
assert R%4==3 and R%B==e and R.bit_length()==2360276 and N.bit_count()==3*B-79
assert R-1>3*B and 2*B<=N.bit_count()-1<3*B
assert (pow(2,R%B,beta)+ports['K0']-F)%beta==0
prime=1000000007
def trim(z):
 while len(z)>1 and z[-1]==0:z.pop()
 return z
def pol(op,a,b):
 if op!='*':return trim([((a[i] if i<len(a) else 0)+(1 if op=='+' else -1)*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
 return trim(z)
env={x:[i+2,i+3] for i,x in enumerate(c['witnesses'])};env.update({x:[y%prime] for x,y in ports.items()})
for name,op,a,b in c['source']:env[name]=pol(op,[a%prime] if isinstance(a,int) else env[a],[b%prime] if isinstance(b,int) else env[b])
assert len(env[c['output']])==51 and env[c['output']][-1]!=0
for packet in (A,D/'reviews/ordinary14-direct-pell79-math-independent'):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(packet/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
 assert not r.stderr and r.stdout==(packet/'result.json').read_bytes()
print(json.dumps({'scope':'external graph and conditional arithmetic reasoning; no Lean/iPRA/PDF conclusion','operations':78,'counts':dict(Counter(row[1] for row in c['source'])),'all_live':True,'q2_coordinate_substitution':True,'degree_lower_ray':50,'ray_prime':prime,'ray_leader':env[c['output']][-1],'author_readme_sha256':hashlib.sha256(readme[:-len(tail)]).hexdigest(),'author_checker_sha256':sha(A/'check.py')},sort_keys=True,indent=2))
