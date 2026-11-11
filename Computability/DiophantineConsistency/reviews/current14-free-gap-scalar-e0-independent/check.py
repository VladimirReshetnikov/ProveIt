from pathlib import Path
import gzip,hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];d=root/'research/current14-free-gap-scalar-e0'
pins={'README.md':'3d16fdcb16255a191258a814641b49fddf50b58141caef5d73f9b0a37c9236db','check.py':'f8a94495f3b7cc2d193498c356ade8ee97f91c96bb0a19f25533f48a085e86d4','result.json':'025b4dffb701d747de53dbc9d73930f5c4d0fca02322a8e43b9f32a48793c53d'}
for n,h in pins.items():assert hashlib.sha256((d/n).read_bytes()).hexdigest()==h,n
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(d/'check.py')])==(d/'result.json').read_bytes()
graph=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';assert hashlib.sha256(graph.read_bytes()).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(graph.read_text());ports={}
for name,meta in g['coefficient_binding']['ports'].items():
 z=(graph.parent/'coefficients'/meta['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==meta['gzip_sha256'];raw=gzip.decompress(z);assert hashlib.sha256(raw).hexdigest()==meta['raw_sha256'];ports[name]=int.from_bytes(raw,'big')
assert set(ports)=={'beta','K0','MC','MF'}
rs={x[0]:x[1:] for x in g['source']};expected={'qm':['*','beta','J'],'q':['+','qm',1],'X':['*','w','q'],'qF':['-','q','F'],'C':['-','qF','alpha'],'gap_product':['*','qm','qF'],'gap':['+','gap_product','alpha'],'rproduct':['*','gap','q2minus1'],'qMF':['*','q','MF'],'maskfactor':['+','MC','qMF'],'mask':['*','maskfactor','J'],'R':['+','rproduct','mask'],'Kw':['+','K0','w'],'transport':['*','Kw','C'],'transport_partial':['+','transport','qF'],'zqm':['*','z','qm'],'Nt':['-','transport_partial','zqm']}
for n,row in expected.items():assert rs[n]==row,n
beta,K,MC,MF=(ports[x] for x in ('beta','K0','MC','MF'));B=beta.bit_length();q=beta+1;assert B==94517 and q==2**B and 0<MC<beta<MF<2*beta and K>0
C=342757;F=C*(K+1)%beta;alpha=q-F-C;assert 0<F<beta and alpha>0 and C>0
gap=beta*(q-F)+alpha;R=gap*(q*q-1)+MC+q*MF;N=(R-1)//2
assert R>=2*B and R%4==3 and R%B==0 and pow(2,(R-B)%B,beta)==1 and (C*(K+1)-F)%beta==0
assert F.bit_length()==47290 and R.bit_length()==378068 and N.bit_count()-1==282615<3*B and R-1>N.bit_count()-1
hx=lambda x:hashlib.sha256(x.to_bytes((x.bit_length()+7)//8,'big')).hexdigest();assert hx(F)=='be5fe0dc508767d0c161c4f799c4594c206ff8b22b42c07b24597676c0ac2f37' and hx(R)=='7d8959244948cd8209556620c04c3112abaced0c03e527bef7bdb730c161d7f0'
print(json.dumps({'status':'PASS_EXTERNAL_ARITHMETIC_REVIEW','port_payloads':4,'scalar_transport':'positive and equals one symbolically','canonical_Y_v2':282615,'q_cubed_v2':283551,'deficit':936,'scope':'Actual-port scalar only; this Y is unusable, no full zero or general exclusion'},indent=2))
