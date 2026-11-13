#!/usr/bin/env python3
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];P=D/'research/sphere70-negative-transport-obstruction';G=D/'research/fourteen-nonzero-spheres/polynomial71.json'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
need(H(P/'check.py')=='c39b53d1b9289bad662ef31840d349d4396300b0479933aeabc2f36403e0e3f0' and H(P/'result.json')=='bf24a3f515900c3a1370c3003a18edc6d28def92f163edef961751089f26075c','packet pins');need(H(G)=='937752350556a94539584db8f646ff9e02d25a7113e6d4af70ac22c1b1e01ad2','sphere graph pin');g=json.loads(G.read_text());r={x[0]:x for x in g['source']}
expected={'qm':['qm','*','beta','J'],'q':['q','+','qm',1],'qF':['qF','-','q','F'],'C':['C','-','qF','alpha'],'Kw':['Kw','+','K0','w'],'transport':['transport','*','Kw','C'],'transport_partial':['transport_partial','+','transport','qF'],'zqm':['zqm','*','z','qm'],'Nt':['Nt','-','transport_partial','zqm'],'PQ2':['PQ2','*','PQ','PQ'],'UW':['UW','*','U','Nt'],'rUW':['rUW','-','UW',1],'rUW2':['rUW2','*','rUW','rUW'],'Z2':['Z2','*','Z','Z'],'sum1':['sum1','+','PQ2','rUW2'],'sum2':['sum2','+','sum1','Z2'],'polynomial':['polynomial','-','sum2',2]};need(all(r[n]==v for n,v in expected.items()),'transport/sphere graph shape')
# Represent affine polynomials in b as (constant, coefficient): q-F=b-1, alpha=b-1.
sub=lambda x,y:(x[0]-y[0],x[1]-y[1]); qF=sub((1,1),(2,0));alpha=(-1,1);C=sub(qF,alpha);need(C==(0,0),'C identity');W=sub(qF,(0,1));need(W==(-1,0),'W identity with C=0 and z=1')
need((1*1)**2+(1*(-1)-1)**2+1**2-2==4 and (1*1)**2+(1*(-1))**2+1**2-3==0,'abstract tuple')
# Check admissible positive bounded cases independently; 63 choices of beta,J and 49 of K,w.
cases=[(beta,J,K,w) for beta in range(1,9) for J in range(1,9) if beta*J>=2 for K in range(1,8) for w in range(1,8)]
for beta,J,K,w in cases:
 b=beta*J;F=2;alpha=b-1;z=1;q=b+1;C=q-F-alpha;W=(K+w)*C+(q-F)-z*b;need(min(beta,J,K,w,F,alpha,z)>0 and C==0 and W==-1,'positive instance')
need(len(cases)==3087,'control count');meta=g['coefficient_binding']['ports']['beta'];z=(D/'research/fourteen-nonzero-spheres/coefficients'/meta['file']).read_bytes();need(hashlib.sha256(z).hexdigest()==meta['gzip_sha256'],'beta compressed');raw=gzip.decompress(z);need(hashlib.sha256(raw).hexdigest()==meta['raw_sha256'] and len(raw)==meta['raw_bytes'] and int.from_bytes(raw,'big')>=2,'beta fixed bytes')
q=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],capture_output=True);need(q.returncode==0 and q.stdout==(P/'result.json').read_bytes(),'author rerun')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','positive_transport_cases':len(cases),'symbolic_transport':'C=0, W=-1','abstract_old':4,'abstract_proposed':0,'fixed_beta_bytes_ge_two':True,'scope':'Transport-only and abstract norm; no full positive zero, existential inequivalence, or Lean theorem.'},indent=2,sort_keys=True))
