#!/usr/bin/env python3
import gzip,hashlib,itertools,json,subprocess,sys
from collections import Counter
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];repo=base.parents[1];p=base/'research/ordinary13-p73-conditional-sphere91'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'README.md':'6206a9145fd1cfc3187276cfebb2fa3c36267fcc4f3975c29628b5a325c8610a','check.py':'60cd125ba5c31511fe8a20dbe4f175404dcd006d8e413d4b5179c9718c34c181','polynomial.json':'3760eb7f48966ff5e550c28a28bb78d23166888679d91ee3b9928f8d79f52242','result.json':'96d052e62d715c2cecc00987e3f9d2081c18a93c5c0f59723012915f737f816d'}.items():assert sha(p/n)==h
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
parentfile=base/'research/ordinary13-p73-triangular91-50/p73_rewrite91_30.json';review=base/'reviews/ordinary13-p73-triangular90-50-independent/check.py';bindingfile=base/'con-zfc-diophantine-forms/72-congruence-sextic/positive13/ACTIVE_BINDING.json'
assert sha(parentfile)=='474152760b9b915e6346f0bff6b41b1db57a3634ed8dd1cf49483c2e5cc36180' and sha(review)=='70e1159e2d433676d8782c2bf4c983a9a25936ad3067f51c7796e1058f884c19' and sha(bindingfile)=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'
subprocess.run([sys.executable,'-I','-S','-B',str(review)],cwd=repo,check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120)
old=json.loads(parentfile.read_text());g=json.loads((p/'polynomial.json').read_text());rows=g['source'];orig=old['source'];assert g['witnesses']==old['witnesses'] and g['fixed_numerals']==old['fixed_numerals'] and len(g['witnesses'])==13 and len(g['fixed_numerals'])==4
expected=[]
for r in orig:
 if r[0]=='Aa':continue
 expected.append(['g88','*','g83','g83'] if r[0]=='g88' else r)
expected.append(['output','-','g91',1]);assert rows==expected and g['output']=='output'
assert len(rows)==91 and Counter(r[1] for r in rows)=={'*':50,'+':24,'-':17}
have=set(g['witnesses']+g['fixed_numerals']);degree={n:1 for n in g['witnesses']};degree.update({n:0 for n in g['fixed_numerals']})
for n,op,a,b in rows:
 assert n not in have and all(type(x)==int or x in have for x in (a,b));d=lambda x:0 if type(x)==int else degree[x]
 degree[n]=d(a)+d(b) if op=='*' else max(d(a),d(b));have.add(n)
need={g['output']}
for n,op,a,b in reversed(rows):
 if n in need:need.update([a,b])
assert all(n in need for n,_,_,_ in rows) and set(g['witnesses']+g['fixed_numerals'])<=need
by={r[0]:r for r in rows}
for r in [['g78','+','V','u'],['y2','*','g78','g78'],['g80','*','V','V'],['g81','-','y2','g80'],['Kaux','*','Delta','f2m'],['g82','*','Kaux','g81'],['g83','-','y2','g82'],['As','-','f2m','g72'],['g72','*','Delta','g71']]:assert by[r[0]]==r
assert degree['Delta']<=4 and degree['f2m']<=2 and degree['V']<=6
# Exact local tail polynomial, verified as coefficient dictionaries.
# (Fa^2 - 1) - (Fa - 1)^2 = 2 Fa - 2.
assert {2:1,0:-1}!={2:1,1:-2,0:1}
left={2:1,0:-1};right={2:1,1:-2,0:1};diff={k:left.get(k,0)-right.get(k,0) for k in set(left)|set(right)};assert {k:v for k,v in diff.items() if v}=={1:2,0:-2}
# Parity controls for the unbounded mod-4 proof; they do not replace it.
for a,f,v,y in itertools.product(range(4),repeat=4):
 D=(a*a+4*a+3)%4;Q=D*(f*f-1)%4;assert D in (0,3) and Q in (0,1);assert (y*y-Q*(y*y-v*v))%4 in (0,1)
B=json.loads(bindingfile.read_text());ports={};fixed={};P=1000000007;assert all(P%d for d in range(2,int(P**.5)+1))
for n,m in B['ports'].items():
 packed=(bindingfile.parent/m['path']).read_bytes();assert hashlib.sha256(packed).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(packed);assert hashlib.sha256(raw).hexdigest()==m['sha256_raw'] and len(raw)==m['raw_bytes'];x=int.from_bytes(raw,'little');assert x>0 and x.bit_length()==m['bits'];ports[n]=x;fixed[n]=x%P
assert ports['beta']==(1<<590069)-1
# Evaluate the needed actual graph subtrees exactly at the explicit positive witness.
variables={x:1 for x in g['witnesses']};mapping={r[0]:r for r in rows}
def eval_node(n):
 if type(n)==int:return n
 if n in variables:return variables[n]
 if n in ports:return ports[n]
 op,a,b=mapping[n][1:];x=eval_node(a);y=eval_node(b);v=x*y if op=='*' else x+y if op=='+' else x-y
 variables[n]=v;return v
deps={'u'}
for n,op,a,b in rows:
 if a in deps or b in deps:deps.add(n)
assert 'R' not in deps
rank=eval_node('R');assert rank>0
variables['u']=rank
assert eval_node('g83')==0 and eval_node('As')==-1215 and eval_node('V')==-rank and eval_node('g78')==0
assert eval_node('Delta')==15 and eval_node('I')==9
rankhash=hashlib.sha256(rank.to_bytes((rank.bit_length()+7)//8,'big')).hexdigest();record=json.loads((p/'result.json').read_text())['explicit_positive_Fa_zero'];assert rankhash==record['rank_unsigned_big_endian_sha256'] and rank.bit_length()==record['rank_bit_length']
# Independently evaluate both complete graphs on an affine weighted ray.
def addp(a,b,s):
 z=[((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%P for i in range(max(len(a),len(b)))]
 while len(z)>1 and not z[-1]:z.pop()
 return z
def mulp(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%P
 while len(z)>1 and not z[-1]:z.pop()
 return z
def ray(graph):
 vals={x:[i+2,i+1] for i,x in enumerate(graph['witnesses'])};vals.update({k:[v] for k,v in fixed.items()})
 for n,op,a,b in graph['source']:
  A=[a%P] if type(a)==int else vals[a];B=[b%P] if type(b)==int else vals[b]
  vals[n]=mulp(A,B) if op=='*' else addp(A,B,1 if op=='+' else -1)
 return vals
v0=ray(old);v1=ray(g);assert len(v1['output'])==31 and v1['output'][-1]==284041780 and len(v0['g83'])<=14
assert v1['output']==addp(v0[old['output']],mulp([2],addp(v0['g83'],[1],-1)),1)
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','author_receipt_reproduced':True,'live_gates':91,'exact_degree':30,'weighted_affine_ray_leader_mod_prime':v1['output'][-1],'prime':P,'positive_witness_Fa':0,'positive_witness_As':-1215,'witness_rank_bit_length':rank.bit_length(),'scope':'External graph and mathematical zero-equivalence; no new Lean, PDF binding, or operation saving.'},indent=2))
