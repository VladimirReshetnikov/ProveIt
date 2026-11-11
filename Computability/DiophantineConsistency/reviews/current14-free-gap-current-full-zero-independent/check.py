from pathlib import Path
import gzip,hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];droot=root/'research/current14-free-gap-current-full-zero'
pins={'README.md':'9b2e67ee822ed797dd9549ef08d72a82cbff842eef5811a3763d17760e89846c','check.py':'ef606f15819837007a8f94b30ab825d4ef71d9e675dfd1c5a4c2105379eadd96','result.json':'cfbca102b7e6c55b64fba888151958ed7e4647900cbf9f07ca72a02efc9f9492'}
for n,h in pins.items():assert hashlib.sha256((droot/n).read_bytes()).hexdigest()==h,n
# Reverse precisely the post-review status/link-only edit, preserving the reviewed mathematical bytes.
text=(droot/'README.md').read_text();tail='\nIndependent external review is recorded in\n`../../reviews/current14-free-gap-current-full-zero-independent/`.\n';assert text.endswith(tail);text=text[:-len(tail)];text=text.replace('independently critically reviewed symbolic construction','author construction awaiting independent critical review').replace('lemmas and old-obstruction hypotheses have passed independent review.','lemmas and old-obstruction hypotheses are submitted for independent review.');assert hashlib.sha256(text.encode()).hexdigest()=='743e45d1b11b49baa72a2ae2c8b902a4b11a210671af8661afa87db304c98dc8'
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(droot/'check.py')])==(droot/'result.json').read_bytes()
# The two inherited reviewed README files received only review-link additions after audit.
for name,tail,oldhash in [('free-pell-gap-generic-completion','\nIndependent external review is recorded in\n`../../reviews/free-pell-gap-generic-completion-independent/`.\n','14201bdce6293c730d62745fae0bb5b92f3c64199fc5c4be87dc51768f212e89'),('free-pell-gap-seed-characterization',"\nIndependent external review is recorded in\n`../../reviews/free-pell-gap-seed-characterization-independent/`. It\nnormalizes the review-link-only edit in the generic completion README when\nchecking that packet's earlier pin.\n",'0f47f871bbffaf1726d0a59d29b391e0442ea7763c4d24ec3f37c33f42a9e2f0')]:
 q=root/'research'/name;text=(q/'README.md').read_text();assert text.endswith(tail) and hashlib.sha256(text[:-len(tail)].encode()).hexdigest()==oldhash;assert subprocess.check_output([sys.executable,'-I','-S','-B',str(q/'check.py')])==(q/'result.json').read_bytes()
graph=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';assert hashlib.sha256(graph.read_bytes()).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(graph.read_text());ports={}
for name,meta in g['coefficient_binding']['ports'].items():
 z=(graph.parent/'coefficients'/meta['file']).read_bytes();assert hashlib.sha256(z).hexdigest()==meta['gzip_sha256'];raw=gzip.decompress(z);assert hashlib.sha256(raw).hexdigest()==meta['raw_sha256'];ports[name]=int.from_bytes(raw,'big')
assert set(ports)=={'beta','K0','MC','MF'}
rs={row[0]:row[1:] for row in g['source']};expected={'qm':['*','beta','J'],'q':['+','qm',1],'X':['*','w','q'],'Y':['*','s','q3'],'E':['*','X','Y'],'k':['+','eta','zeta'],'kY':['*','k','Y'],'ell':['*','E','kY'],'c':['+','kY','eta'],'a':['+','E','Y'],'Delta':['+','a2','H'],'main_root':['+','main_base','gammaH'],'N0':['-','tau2','first_product'],'N1':['-','main_square','Dc2'],'Nt':['-','transport_partial','zqm'],'normalized_S':['*','i','Dc2'],'scaled_Ns':['-','scaled_f2','normalized_S2']}
for n,v in expected.items():assert rs[n]==v,n
beta,K,MC,MF=(ports[n] for n in ('beta','K0','MC','MF'));B=beta.bit_length();q=beta+1;assert B==94517 and q==2**B and 0<MC<beta<MF<2*beta and K>0
e,C=28633,1;F=(K+pow(2,e,beta))%beta;alpha=q-F-C;assert 0<F<beta and alpha>0 and C>0
gap=beta*(q-F)+alpha;R=gap*(q*q-1)+MC+q*MF;assert R%4==3 and (R+1)%3==0;dd=(R+1)//3;assert dd%4==0
r,h,lam=2*dd,3*dd//2,dd-1;assert r%B==e and r>=2*B and lam>=3*B and r+lam==R and 2*h==R+1 and h%2==0 and r%2==0
assert (r-1)*(1+r+lam)-1-(h-1)*(2+r+2*lam)==lam
assert r-1>=h-1 and (2*dd-1).bit_length()<=dd-1 and h.bit_length()<=r+2*lam and dd>=8
assert ((K+pow(2,e,beta))*C-F)%beta==0 and R>=26 and R+1<q**4-q**3<q**4
hx=lambda x:hashlib.sha256(x.to_bytes((x.bit_length()+7)//8,'big')).hexdigest();assert F.bit_length()==47272 and hx(F)=='411970036963b7b05d9055fb1917f3f0f636892cdf4e85b9930272e4acf56cca' and R.bit_length()==378068 and hx(R)=='3dd9c6439028ac65f4ec83ba0589e74a74221764c6d2ba342a7bd5902e9d7d3e'
assert R.bit_count()==283517 and ((R-1)//2).bit_count()-1==283515 and 283515<3*B and R-1>283515
# Exact small versions independently test the noncanonical ratio and seed construction.
def unit(u,n):
 D=u*u-1;x,y=1,0
 for _ in range(n):x,y=u*x+D*y,x+u*y
 return x,y
controls=[]
for dd0 in (4,8,12,16):
 r0,h0,lam0=2*dd0,3*dd0//2,dd0-1;RR=3*dd0-1;X,Y=2**r0,2**lam0;E=X*Y;m=E*Y;P=2*m+1;A=E+Y+2;tau,ks=unit(P,h0);k=2*ks;D,c=unit(A,r0);eta=c-Y*k;zeta=k-eta
 assert Y*k<c<(Y+1)*k and eta>0 and zeta>0 and E==2**RR
 n,rem=divmod(tau-k+RR,E);assert rem==0 and n>0 and tau==E*n+k-RR and tau*tau-m*(m+1)*k*k==1
 H=4*(E+Y)+3;gamma,rem=divmod(D-X-(E+Y)*c,H);assert rem==0 and gamma>0 and D*D-(A*A-1)*c*c==1
 controls.append({'d':dd0,'strict_ratio':True,'positive_n_gamma':True})
for review in ('current14-carrier64-bad-gap-exclusion-independent','current14-carrier64-pell-floor-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/review/'check.py')],check=True,stdout=subprocess.DEVNULL,timeout=180)
print(json.dumps({'status':'PASS_SYMBOLIC_EXTERNAL_REVIEW','actual_ports':4,'F_bits':F.bit_length(),'R_bits':R.bit_length(),'old_canonical_Y_v2':283515,'q_cubed_v2':283551,'old_valuation_deficit':36,'small_seed_controls':controls,'actual_witness_expanded':False,'scope':'Actual-port free-gap symbolic candidate zero; same-q,R maintained exclusion conditional on historical P72 binding; no unrestricted nonequivalence or Lean'},indent=2))
