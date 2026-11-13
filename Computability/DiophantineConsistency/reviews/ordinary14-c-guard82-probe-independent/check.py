#!/usr/bin/env python3
"""Independent C-guard actual-port seed, ray, and source-map review; no Lean."""
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-c-guard82-probe';Q=D/'reviews/ordinary13-folded-root86-toy-full-zero-independent'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in [(P/'README.md','717f18e891420fb469e18c76c01d83698948c42ae6a7b1fe3eabc8caf81db2c2'),(P/'check.py','ba6eaf721f92c39cdbc173d2fdd96252bb808af502ca2adb2e41513ac442ce73'),(P/'candidate.json','0f0c1a2be4c62a940384bbae4d16c02caef31d7eefd82dda9ddfb1437236cf57'),(P/'result.json','ebe1902b44f241a229722b959ce9cd52dac120f13f47c2fca52c6c92b57db85e'),(Q/'check.py','19b05a2069655a6eacfa91d0824afad080fe83201ba358da3e710c66b431752b'),(Q/'result.json','900aebfa8b65363d44e889525fc0eeb6c0b6b6c356fdec94f99db8f43260bf3a')]:assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent mathematical review is recorded in\n`../../reviews/ordinary14-c-guard82-probe-math-independent/`.\nA separate independent decoder review is recorded in\n`../../reviews/ordinary14-c-guard82-probe-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='6ac02122308f2b1fdfc70d6d4b0bfac559805bc421a9d0648fad4bcb12515e29'
for p in (P,Q):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
base=D/'Lean/DiophantineConsistency/Compact44';forward=base/'FreeJ13Halt.lean';power=base/'FreeJPowerFinish.lean';assert sha(forward)=='18b17a1c81e6ff58d74fd6a7160948b75c71203ee8f5c3bd29e4d3fc9a76218a' and sha(power)=='e4b2e84586b6232b9accc7775f094d4e1047453f1e8337f6241d39a6657d8816'
src=forward.read_text();assert 'theorem forward' in src and 'let x : Fin 12 → V := ![v 0, v 1, v 2, t, v 5, v 6, v 7, v 8, v 9, v 10, v 4 + v 11, v 12]' in src and 'refine ⟨x, ?_, ?_⟩' in src
src=power.read_text();assert 'theorem graph_power' in src and '(hbeta : (46:V)≤(p 0:V))' in src and 'v 5=Exp.exp R' in src
g=json.loads((P/'candidate.json').read_text());old=D/'research/ordinary14-shifted-guard87-probe/candidate.json';assert sha(old)=='405dbed5bf465dacac2246e6e8b2c53bcb3dda9b4b13ba277f4a18cdd43ae210';og=json.loads(old.read_text());expected=[]
for row in og['source']:
 if row[0] in ('g25','g26','g27','guard_base','bt_quotient'):continue
 expected.append(['guard','-','C','omega'] if row[0]=='guard' else row)
assert g['source']==expected and len(expected)==82 and g['fixed_numerals']==[x for x in og['fixed_numerals'] if x!='K0']
known=set(g['witnesses']+g['fixed_numerals']);used={'guarded_out'}
for n,op,a,b in expected:assert n not in known and all(isinstance(x,int) or x in known for x in (a,b));known.add(n)
for n,op,a,b in reversed(expected):
 if n in used:used.update(x for x in (a,b) if isinstance(x,str))
assert all(r[0] in used for r in expected) and set(g['witnesses']+g['fixed_numerals'])<=used
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';bp=root/'ACTIVE_BINDING.json';other=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json';assert sha(bp)=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf' and sha(other)=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01';B=json.loads(bp.read_text());C0=json.loads(other.read_text());ports={}
for n,m in B['ports'].items():
 assert C0['ports'][n]['sha256_raw']==m['sha256_raw'] and C0['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=(root/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(z);assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw'];ports[n]=int.from_bytes(raw,'little')
beta=ports['beta'];K=ports['K0'];MC=ports['MC'];MF=ports['MF'];bits=590069;assert beta==(1<<bits)-1;q=beta+1;HP=MF-beta;C=beta-MC;F=q-HP;alpha=HP-C
assert 0<MC<beta and 0<HP<beta and 0<alpha<beta and 0<C<q and F>0 and 0<=K<q*q
G=beta*(q-F)+alpha;R=G*(q*q-1)+MC+q*MF;N=(R-1)//2;assert R%4==3 and R>=2*bits and R.bit_length()==2360161 and N.bit_count()==1770208
e=(R-bits)%bits;res=(C*(K+pow(2,e,beta))-F)%beta;assert res and res.bit_length()==590003 and hashlib.sha256(res.to_bytes((res.bit_length()+7)//8,'big')).hexdigest()=='ce55ad184bb41a6cd4d218547b8c3b4950fa42aba22e127057bd2ebbff092f95'
# Independent nonuniform affine ray modulo the actual-port reduction.
mod=1000000007;env={n:[i+1,i+2] for i,n in enumerate(g['witnesses'])};env.update({n:[v%mod] for n,v in ports.items()})
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def calc(op,x,y):
 if op!='*':return trim([((x[i] if i<len(x) else 0)+(1 if op=='+' else -1)*(y[i] if i<len(y) else 0))%mod for i in range(max(len(x),len(y)))])
 z=[0]*(len(x)+len(y)-1)
 for i,a in enumerate(x):
  for j,b in enumerate(y):z[i+j]=(z[i+j]+a*b)%mod
 return trim(z)
for n,op,a,b in expected:env[n]=calc(op,[a%mod] if isinstance(a,int) else env[a],[b%mod] if isinstance(b,int) else env[b])
assert len(env['guarded_out'])==27 and env['guarded_out'][-1]!=0
print(json.dumps({'status':'PASS_SCOPED_ACTUAL_PORT_C_GUARD_ZERO','operations':82,'rank_bits':R.bit_length(),'N_popcount':N.bit_count(),'omitted_transport_nonzero':True,'weighted_ray_degree':26,'weighted_ray_leader':env['guarded_out'][-1],'scope':'symbolic actual-port C-guard zero; fixed-q,R parent obstruction conditional on source proof-body replay; no unrestricted nonequivalence or Lean'},indent=2))
