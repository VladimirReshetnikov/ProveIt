from pathlib import Path
from hashlib import sha256
import json,sys,random,math
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta-zeta84-free-square-obstruction')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
G=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
assert G['witnesses'][3]=='n_f' and len(G['source'])==85
rows=[]
for n,op,a,b in G['source']:
 if n=='rho':
  assert (op,a,b)==('-','f2',1);continue
 if n=='f2':
  assert (op,a,b)==('*','n_f','n_f');n,op,a,b='f2','+','n_t',1
 a='n_t' if a=='rho' else a;b='n_t' if b=='rho' else b
 rows.append([n,op,a,b])
w=G['witnesses'].copy();w[3]='n_t';assert len(rows)==84
child={'name':'free-square-minus-one boundary candidate; no unrestricted zero-equivalence claimed','domain':G['domain'],'witnesses':w,'fixed_numerals':G['fixed_numerals'],'source':rows,'output':G['output']}
encoded=(json.dumps(child,indent=2)+'\n').encode()
if '--write' in sys.argv:(D/'candidate.json').write_bytes(encoded)
else:assert (D/'candidate.json').read_bytes()==encoded
def ev(graph,ws,ports,mod=None):
 d=dict(zip(graph['witnesses'],ws));d.update(zip(graph['fixed_numerals'],ports))
 for n,op,a,b in graph['source']:
  x=d[a] if isinstance(a,str) else a;y=d[b] if isinstance(b,str) else b
  z={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
  d[n]=z if mod is None else z%mod
 return d
rng=random.Random(361908);mod=1000000007
for _ in range(300):
 v=[rng.randrange(15) for i in range(13)];v[3]=rng.randrange(1,15);ports=[rng.randrange(-5,7) for i in range(4)]
 u=v.copy();u[3]=v[3]**2-1;old=ev(G,v,ports,mod);new=ev(child,u,ports,mod)
 assert all(old[n]==new[n] for n in ('A0','A1','Q','I','g72','Fa','out'))
v=[1,0,0,16875,0,1,0,0,0,15,4,202499,0];ports=[-1,-1,20,0]
d=ev(child,v,ports);fields={k:d[k] for k in ('q','kbase','Bt','Z','R','A0','A1','f2','Q','I','g72','V','Fa','out')}
assert fields=={'q':0,'kbase':19,'Bt':1,'Z':-1,'R':18,'A0':0,'A1':0,'f2':16876,'Q':50625,'I':225,'g72':0,'V':202497,'Fa':1,'out':0}
assert math.isqrt(d['f2'])==129 and 129**2<d['f2']<130**2
# For the same other coordinates, parent output zero implies (1+g72)=±1;
# its residue is never -1 mod 4, so f²=16876, impossible.
for f in range(4):assert (1+225**2-3*(f*f-1))%4!=3
print(json.dumps({'parent_rows':85,'candidate_rows':84,'forward_positive_f_controls':300,'signed_noncompact_ports':ports,'child_witness':v,'full_child_fields':fields,'parent_same_other_coordinates_impossible_by_mod4':True,'compact_port_or_existential_nonequivalence_proved':False,'lean_executed':False},sort_keys=True,indent=2))
