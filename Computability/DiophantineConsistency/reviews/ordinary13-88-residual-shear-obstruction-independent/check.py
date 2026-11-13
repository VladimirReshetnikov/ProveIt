#!/usr/bin/env python3
"""Independent actual-port ray for bounded residual shears; no Lean."""
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary13-88-residual-shear-obstruction';Q=D/'reviews/ordinary13-four-square88-30-independent'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in [(P/'README.md','b8b68fb246333c014d222d936b1140772b2ff133108525afb22524eba8fae77d'),(P/'check.py','05119198a43577e3683c815442f9ddb6c93637cfa329aa815a3cb324d9d0f314'),(P/'result.json','04fff12b1cb69d39965ea887bf41c770d6d990f83a6930079b1a8f2a083eed13'),(Q/'check.py','0883709a84091c0c6ff099bbf39bb9a60bf9a3f4cff7433f83a2718ade027167'),(Q/'result.json','50ff79fdffe3b91724b8da9f5dad19ffb5a14bcaf4cf57737b4db29366048f86')]:assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary13-88-residual-shear-obstruction-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='09a513895d2c7e125b9b1a7742e2573f98bceb2f3fa15559dda96c4d40b2eb20'
for p in (P,Q):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not r.stderr and r.stdout==(p/'result.json').read_bytes(),p
graph=D/'research/ordinary13-four-square88-30/candidate.json';assert sha(graph)=='daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420';g=json.loads(graph.read_text());rows={r[0]:r for r in g['source']}
for n,row in {'Dstar':['Dstar','+','g58','g59'],'g58':['g58','*','U','b0'],'b0':['b0','+','X','g19'],'g19':['g19','*','a','c'],'g59':['g59','*','H','shift'],'Delta':['Delta','+','H','g17'],'g17':['g17','*','a','a'],'A1':['A1','-','g61','g65']}.items():assert rows[n]==row
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';bp=root/'ACTIVE_BINDING.json';other=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json';assert sha(bp)=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf' and sha(other)=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01';B=json.loads(bp.read_text());C=json.loads(other.read_text());mod=1000000007;ports={}
for n,m in B['ports'].items():
 assert C['ports'][n]['sha256_raw']==m['sha256_raw'] and C['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=(root/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(z);assert hashlib.sha256(raw).hexdigest()==m['sha256_raw'] and len(raw)==m['raw_bytes'];ports[n]=int.from_bytes(raw,'little')%mod
assert all(mod%d for d in range(2,int(mod**0.5)+1))
# A sparse univariate implementation independent of the author's list code.
def plus(a,b,sgn=1):
 z=a.copy()
 for k,v in b.items():z[k]=(z.get(k,0)+sgn*v)%mod
 return {k:v for k,v in z.items() if v} or {0:0}
def times(a,b):
 z={}
 for i,x in a.items():
  for j,y in b.items():z[i+j]=(z.get(i+j,0)+x*y)%mod
 return {k:v for k,v in z.items() if v} or {0:0}
def ray(special):
 v={n:{1:1} for n in g['witnesses']};v.update({n:{0:x} for n,x in ports.items()})
 if special:v.update({'f':{0:0},'i':{0:0},'u':{0:0},'gamma':{1:(-ports['beta']*(ports['beta']-1))%mod}})
 def get(x):return {0:x%mod} if isinstance(x,int) else v[x]
 for n,op,a,b in g['source']:v[n]=times(get(a),get(b)) if op=='*' else plus(get(a),get(b),1 if op=='+' else -1)
 return {n:(max(v[n]),v[n].get(max(v[n]),0)) for n in ('A0','A1','Fam','g72')}
ordinary=ray(False);special=ray(True);assert [ordinary[n][0] for n in ('A0','A1','Fam','g72')]==[15,13,13,10]
assert special['A0']==(15,142738814) and special['A1'][0]<=12 and special['Fam'][0]<=12 and special['g72'][0]<=9
print(json.dumps({'status':'PASS_BOUNDED_SHEAR_OBSTRUCTION','ordinary_degrees':[ordinary[n][0] for n in ('A0','A1','Fam','g72')],'special_degrees':[special[n][0] for n in ('A0','A1','Fam','g72')],'special_A0_leader':special['A0'][1],'scope':'integer-polynomial residual multipliers P,Q degree<=2 and S<=5 only; no zero-equivalence or global minimality; no Lean'},indent=2))
