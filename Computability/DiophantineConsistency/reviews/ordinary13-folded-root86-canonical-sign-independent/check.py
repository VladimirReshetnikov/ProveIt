#!/usr/bin/env python3
import gzip,hashlib,json,re,subprocess,sys
from collections import defaultdict
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
base=Path(__file__).resolve().parents[2];repo=base.parents[1];p=base/'research/ordinary13-folded-root86-canonical-sign'
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'README.md':'fdd753dd5295f03c21456988d4d9d27b39ac8abc10fad235ef299d943a723d20','check.py':'a89b60d04f5b387f8d76c87759294430268ce175f80376309b282f13de2479f3','result.json':'efdb46db3a1931e907c1fd6b9ced3942f5c8b4c5861808cea559e5888741901f'}.items():assert sha(p/n)==h
readme=(p/'README.md').read_bytes();tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary13-folded-root86-canonical-sign-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='ff92c3b27aa38a083d9db5d3fd58f236f401e83fd2135c79c999df0b4b4acd31'
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
extra={'ArithmeticPacking.lean':'3cb27eae0e99b3ab11c76d0e1b279d2b4652d4d662944719e213f81235fbb2f1','ArithmeticPellRecurrence.lean':'63ec2a49f8d7066dbd8647a663db4bbd7255abd3ca7c3cc0d4d7b3533a189b16','Compact44/CompactRankResidueJoin.lean':'37c91ed83d751bc4e55d559572a857dae302f87250dde6f5a7231bca12fb0c46','Compact44/CompactPellOrdinateCompat.lean':'9df8902913d69687b21d651f9422b021b73bef03a81a6503d327d221270fce91','Compact44/CompactPositiveValuation.lean':'6eaa5edffa95f91ed91bacc88ec647b71125deacc9edca8ac03748940a73c22d','Compact44/CompactSymbolicModelIff.lean':'379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46','Compact44/CompactSymbolicModelUnconditionalIff.lean':'ea2dbe86aaebf241d233a1cde5860157da34cf2e20ae943aef42516c659888aa','Compact44/CompactCellProductBound.lean':'bdf642a54f609caf3a09d08ea529079fbc201414ac390566fd5c10a88a9a2c22'}
L=base/'Lean/DiophantineConsistency';files={}
for n,h in extra.items():q=L/n;assert sha(q)==h;files[n]=q.read_text()
pack=files['ArithmeticPacking.lean'];join=files['Compact44/CompactRankResidueJoin.lean'];val=files['Compact44/CompactPositiveValuation.lean'];mi=files['Compact44/CompactSymbolicModelIff.lean'];rec=files['Compact44/CompactPellOrdinateCompat.lean']
for s in ('N_gt : 1 < N','theorem C_add_F_lt','theorem C_pos','theorem F_pos','theorem packing_alpha'):assert s in pack
for s in ('2*(590069*N) < rank K N s X','rank_properties h','CompactPackingOriginResidue.packing_origin_mod_four h','CompactLowModFour.low_mod_four'):assert s in join
assert 'auxT, Exp.exp R, Y, r, eta, zeta' in val and 'halt_positive_zero_of_ports T p hT' in mi and 'theorem ordinate_add_ge' in rec
assert 'theorem symbolic_kernel_lt : (paramKernel rho : V) < Exp.exp (592884 : V)' in files['Compact44/CompactCellProductBound.lean']
halt=(L/'Compact44/FreeJHaltModelZero.lean').read_text();back=(L/'Compact44/FreeJ13Halt.lean').read_text();first=(L/'Compact44/CompactHaltFirstSeed.lean').read_text();transfer=(L/'Compact44/CompactFirstTransportSeed.lean').read_text();outer=(L/'ArithmeticOuterSeed.lean').read_text()
for s in ('halt_first_gamma T hT','let N := haltLength T','let R := rank K N stride X','let q := Exp.exp u','let v := valuation K N stride X sY f auxT r eta zeta i auxw y gamma','have hv7 : v 7=r := rfl','hBt hfirsteq'):assert s in halt
assert 'let w : Fin 13 → V := ![v 0, v 1, v 2, 1 + v 3, i, v 4, v 5, v 6, v 7, v 8, v 9, u, v 11]' in back
for s in ('(q*K+Exp.exp R)*C = q*F+(q-1)*(q*z)','(q^3*(q-1))*(ell+k+r)+Y*(q-1)','(q^3*(q-1))*tau+(1+(q-1)*k)*q^3*((q-1)*(q*z))'):assert s in first and s in transfer
assert 'tau*tau=1+(E*Y)*(E*Y+1)*k*k' in outer and 'R=2*r+1' in outer and 'k=2*ycoord (r+1)' in outer
# Exact polynomial rearrangement after cancelling M=q³(q−1)>0. The source
# first equation becomes ell+k+r+s = tau+(1+b*k)*q*z, and Bt=b*q*z.
def at(x):return {(x,):1}
def add(a,b,s=1):
 d=defaultdict(int,a)
 for k,v in b.items():d[k]+=s*v
 return {k:v for k,v in d.items() if v}
def mul(a,b):
 d=defaultdict(int)
 for x,u in a.items():
  for y,v in b.items():d[tuple(sorted(x+y))]+=u*v
 return {k:v for k,v in d.items() if v}
one={():1};ell,k,rr,ss,b,q,z,tau=map(at,('ell','k','r','s','b','q','z','tau'));qz=mul(q,z);bt=mul(b,qz)
source_relation=add(add(add(add(ell,k),rr),ss),add(mul(add(one,mul(b,k)),qz),tau),-1)
target_relation=add(add(add(add(add(rr,mul(k,bt),-1),tau,-1),ell),k),add(ss,qz,-1))
assert source_relation==target_relation
# Multiply by 16 to check the tau < ell+3k/4 Pell-square difference.
m=at('m');ell=mul(m,k);lhs=add(mul(add(mul({():4},ell),mul({():3},k)),add(mul({():4},ell),mul({():3},k))),mul({():16},add(one,mul(mul(m,add(m,one)),mul(k,k)))),-1)
rhs=add(mul(add(mul({():8},m),{():9}),mul(k,k)),{():16},-1);assert lhs==rhs
P=base/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';bp=P/'ACTIVE_BINDING.json';p115=base/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json'
assert sha(bp)=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf' and sha(p115)=='dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01';B=json.loads(bp.read_text());C=json.loads(p115.read_text());v={}
for n,m0 in B['ports'].items():
 assert C['ports'][n]['sha256_raw']==m0['sha256_raw'] and C['ports'][n]['sha256_gzip']==m0['sha256_gzip'];z=(P/m0['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m0['sha256_gzip'];raw=gzip.decompress(z);assert hashlib.sha256(raw).hexdigest()==m0['sha256_raw'] and len(raw)==m0['raw_bytes'];v[n]=int.from_bytes(raw,'little');assert v[n]>0 and v[n].bit_length()==m0['bits']
assert v['beta']==(1<<590069)-1 and v['K0'].bit_length()==592884 and v['K0'].bit_length()<2*590069 and 581197**4>=2
# Independently compare every literal Lean operation to the retained 87 graph.
gp=base/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive13_87_degree51.json'; lp=L/'Compact44/FreeJ13.lean'; g88=base/'research/ordinary13-four-square88-30/candidate.json'
for path,digest in ((gp,'24b9120cc07693ba3fab0bff254c071fae800d14415850c3411651c026e28f0c'),(lp,'cf8beb3993b1cd716266d7adf06ab9ee4eda5d5a7e4b921072eecc5b31389d01'),(g88,'daaae50a0837b0b79d2d911daad222664194407e94522154e655a1b1a3cfd420')): assert sha(path)==digest
g=json.loads(gp.read_text());g2=json.loads(g88.read_text());assert len(g['source'])==87 and len(g2['source'])==88 and g['witnesses']==g2['witnesses'] and g['witnesses'][8]=='r' and g['fixed_numerals']==g2['fixed_numerals']
block=lp.read_text().split('-- BEGIN LITERAL GRAPH\n',1)[1].split('  -- END LITERAL GRAPH',1)[0]; rows=[]
for line in block.splitlines():
 match=re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)',line);assert match,line
 name,a,op,bb=match.groups();rows.append([name,op,int(a) if a.isdecimal() else a,int(bb) if bb.isdecimal() else bb])
assert rows==g['source']
old={row[0]:row for row in g['source']};new={row[0]:row for row in g2['source']};assert {n for n in old.keys()&new.keys() if old[n]!=new[n]}=={'g80','g81'}
assert old['g78']==['g78','+','V','u'] and old['g80']==['g80','*','V','V'] and old['g81']==['g81','-','y2','g80'] and new['g80']==['g80','+','g78','V'] and new['g81']==['g81','*','u','g80']
assert old['y2']==new['y2']==['y2','*','g78','g78']
rp=base/'reviews/ordinary13-four-square88-30-independent';assert sha(rp/'check.py')=='0883709a84091c0c6ff099bbf39bb9a60bf9a3f4cff7433f83a2718ade027167' and sha(rp/'result.json')=='50ff79fdffe3b91724b8da9f5dad19ffb5a14bcaf4cf57737b4db29366048f86'
r=subprocess.run([sys.executable,'-I','-S','-B',str(rp/'check.py')],cwd=repo,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120);assert not r.stderr and r.stdout==(rp/'result.json').read_bytes()
print(json.dumps({'status':'PASS_SCOPED_SOURCE_TRACE','author_receipt_reproduced':True,'extra_source_files_pinned':len(extra),'literal_lean_graph_rows':len(rows),'reviewed_88_receipt_reproduced':True,'beta_bits':v['beta'].bit_length(),'K0_bits':v['K0'].bit_length(),'scope':'Conditional standard-natural halt witness and retained source trace; no halt, arbitrary-zero conclusion, Lean replay or file binding.'},indent=2))
