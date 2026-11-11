#!/usr/bin/env python3
"""Independent CRT/valuation reconstruction and source-boundary audit; no Lean."""
import gzip,hashlib,json,math,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary13-folded-root86-negated-compact44-seed';toy=D/'reviews/ordinary13-folded-root86-toy-full-zero-independent';floor=D/'reviews/current14-carrier64-pell-floor-independent'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in [(P/'README.md','7d1dc11038b1d12bb7862a226aabf1742823523bcc34adf9a7c82b7e3905c6f5'),(P/'check.py','e64afc3b2e1de86e0d61d50b114fc13bfa268fa68db3ecde2bfcb6cde648764a'),(P/'result.json','5a781e806480d779095ce81d8481856fb0fe88946e9d980122a9013232912421'),(toy/'check.py','19b05a2069655a6eacfa91d0824afad080fe83201ba358da3e710c66b431752b'),(toy/'result.json','900aebfa8b65363d44e889525fc0eeb6c0b6b6c356fdec94f99db8f43260bf3a'),(floor/'check.py','65ff9800b15d3313eaecb3f595851f355f9e7b0c8f811afd46187cc95c9f6839'),(floor/'result.json','042e585bfc7e47b8212eabeb5271cdb8b2e5e9b64f28e53e995f2690fbe9b0b3')]:assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary13-folded-root86-negated-compact44-seed-independent/`.\nIt independently reconstructs the scalar seed and checks the symbolic Pell\nsteps. Its same-q, same-R parent obstruction does not exclude parent zeros\nat other q or R.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='a83ca2a55a847d3f5cc72f597acff2da858f85c5a65f51fca3b7e96e7124adac'
# Reproduce prior source-only generic controls; no Lean or provider rebuild.
for p in (toy,floor):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
graph=D/'research/ordinary13-folded-root86-negated/candidate.json';assert sha(graph)=='186471e8454b9443df2234b25380d6b34d494e951648291645cc492a6d646166';g=json.loads(graph.read_text());rows={x[0]:x for x in g['source']}
for name,row in {'qm':['qm','*','J','beta'],'C':['C','-','qF','alpha'],'Bt':['Bt','-','g27','g28'],'G':['G','+','alpha','g44'],'R':['R','+','g47','g50'],'g31':['g31','-','g30','r'],'Z':['Z','-','g34','folded_q3Bt'],'A0':['A0','-','g38','g42'],'A1':['A1','-','g61','g65'],'Fa':['Fa','-','y2','g82'],'g72':['g72','-','g71','Q']}.items():assert rows[name]==row
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';bp=root/'ACTIVE_BINDING.json';p115=D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json';assert sha(bp)=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf' and sha(p115)=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01';B0=json.loads(bp.read_text());C=json.loads(p115.read_text());ports={}
for n,m in B0['ports'].items():
 assert C['ports'][n]['sha256_raw']==m['sha256_raw'] and C['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=(root/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(z);assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw'];ports[n]=int.from_bytes(raw,'little')
B=590069;beta=ports['beta'];K=ports['K0'];MC=ports['MC'];MF=ports['MF'];q=beta+1;Q=q*q-1
assert beta==(1<<B)-1 and K>=0 and 0<MC<beta<MF<2*beta and math.gcd(K+1,beta)==math.gcd(Q,B)==math.gcd(beta,B)==1
# Build the CRT solution with a generic pairwise-merging algorithm rather
# than the author's direct substitution sequence.
def merge(x,mod,r,n):
 assert math.gcd(mod,n)==1
 return x+mod*((r-x)*pow(mod,-1,n)%n),mod*n
r_beta=(-pow(K+1,-1,beta))%beta;r_B=(-(beta*beta*Q+MC+q*MF)*pow(Q,-1,B))%B
alpha0,mod=merge(0,1,r_beta,beta);alpha0,mod=merge(alpha0,mod,r_B,B);alpha0,mod=merge(alpha0,mod,MC%4,4);assert mod==4*B*beta
if alpha0<=beta:alpha0+=mod
R0=(beta*beta+alpha0)*Q+MC+q*MF; L=R0.bit_length()+1; S=(mod*Q).bit_length()+1
alpha=alpha0+mod*sum(1<<(L+j*S) for j in range(4));R=(beta*beta+alpha)*Q+MC+q*MF;N=(R-1)//2
assert alpha>beta and R>2*B and R%B==0 and R%4==3 and R%3==0 and (alpha*(K+1)+1)%beta==0
count=sum(x.bit_count() for x in N.to_bytes((N.bit_length()+7)//8,'little'));assert count==N.bit_count()==5379471 and count-1>=3*B and R.bit_length()==9441197
def digest(n):return hashlib.sha256(n.to_bytes((n.bit_length()+7)//8,'big')).hexdigest()
result=json.loads((P/'result.json').read_text());assert digest(R)==result['R_sha256_be'] and digest(alpha)==result['alpha_sha256_be'] and count==result['N_popcount']
print(json.dumps({'status':'PASS_SCOPED_ACTUAL_PORT_SYMBOLIC_ZERO','independent_CRT':True,'rank_bits':R.bit_length(),'N_popcount':count,'Y_two_adic_valuation':count-1,'inherited_toy_and_floor_receipts':True,'scope':'actual compact44 signed-candidate symbolic zero under cited external Pell identities; no Lean, halt, parent zero, or unrestricted nonequivalence claim'},indent=2))
