#!/usr/bin/env python3
"""Pin source route and compact44 bytes; finite bounds only, no Lean."""
import gzip,hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h;return b
base='Lean/DiophantineConsistency/Compact44/'
paths={
'CompactHaltPackedWord.lean':'5c2a951c912be180a78f38f8da743bee4f7a0d6ee8e588fc45bd044962ab0cc5',
'CompactConstructedRank.lean':'fd50c742a6b3b728ec41efc9529289b6f11029054ae83bc87a02de516be02b92',
'CompactFirstTransportSeed.lean':'c863672c57c0d17b104d1b559d01af34bc33967d4baf1f056d1ad1c95901fc10',
'CompactFirstSeed.lean':'a5342a7ec9a11ddc4b6054089693c294821fbc27cacb3ceef7c670fcbbbbf91a',
'CompactSeedOrdinate.lean':'d7141305340a682947e88f68fa65305aa3de643c3f31790ce6a846a7bacd0af5',
'CompactFirstPositive.lean':'dce31c66f5336a822ad9c27dbb5a2d1af25bf977c223cd366399d5345e7e2c8f',
'CompactHaltFirstSeed.lean':'029299a28948d9769aac686a85d9b7a270e567c9f96493330bca112a35a1ef12',
'CompactHaltFirstGamma.lean':'96cfece73e45b4734b738063de08663c6fc8c704d04f75fe7801c5a7608e87c4',
'FreeJHaltModelZero.lean':'9307b3bbc8f03b4cf63e0fff49e2b1f3c1204894739653f70aa3e71b10dc1447',
'FreeJ13Halt.lean':'18b17a1c81e6ff58d74fd6a7160948b75c71203ee8f5c3bd29e4d3fc9a76218a'}
src={n:pin(base+n,h).decode() for n,h in paths.items()}
extra={'ArithmeticPacking.lean':'3cb27eae0e99b3ab11c76d0e1b279d2b4652d4d662944719e213f81235fbb2f1','ArithmeticPellRecurrence.lean':'63ec2a49f8d7066dbd8647a663db4bbd7255abd3ca7c3cc0d4d7b3533a189b16','Compact44/CompactRankResidueJoin.lean':'37c91ed83d751bc4e55d559572a857dae302f87250dde6f5a7231bca12fb0c46','Compact44/CompactPellOrdinateCompat.lean':'9df8902913d69687b21d651f9422b021b73bef03a81a6503d327d221270fce91','Compact44/CompactPositiveValuation.lean':'6eaa5edffa95f91ed91bacc88ec647b71125deacc9edca8ac03748940a73c22d','Compact44/CompactSymbolicModelIff.lean':'379616890bb253e86d6defdc2424793e187be8c949e7a186d231bb024c2f1f46','Compact44/CompactSymbolicModelUnconditionalIff.lean':'ea2dbe86aaebf241d233a1cde5860157da34cf2e20ae943aef42516c659888aa','Compact44/CompactCellProductBound.lean':'bdf642a54f609caf3a09d08ea529079fbc201414ac390566fd5c10a88a9a2c22'}
extra_src={n:pin('Lean/DiophantineConsistency/'+n,h).decode() for n,h in extra.items()}
assert 'theorem symbolic_kernel_lt : (paramKernel rho : V) < Exp.exp (592884 : V)' in extra_src['Compact44/CompactCellProductBound.lean']
outer=pin('Lean/DiophantineConsistency/ArithmeticOuterSeed.lean','cc45baaa9dd7782afad29edbbcb8199926b4d2b8161ff4cb71204eda8eb897dc').decode()
for n,s in [('CompactHaltPackedWord.lean','power 581197 ((2*T+3)+1)'),('CompactConstructedRank.lean','2*(590069*N) < rank'),('CompactFirstPositive.lean','ell+k+r+s=(1+(q-1)*k)*b+tau'),('CompactSeedOrdinate.lean','ycoord (2:V) b=2*(b+2)'),('FreeJHaltModelZero.lean','have hv7 : v 7=r := rfl'),('FreeJ13Halt.lean','v 6, v 7, v 8, v 9, u, v 11')]: assert s in src[n]
assert 'k=2*ycoord (r+1)' in outer and 'tau*tau=1+(E*Y)*(E*Y+1)*k*k' in outer
p=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';b=json.loads(pin(str((p/'ACTIVE_BINDING.json').relative_to(D)),'6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'))
b115=json.loads(pin('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'))
v={}
for n,m in b['ports'].items():
 assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=(p/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(z);assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw'];v[n]=int.from_bytes(raw,'little')
B=590069;assert v['beta']==2**B-1 and v['K0'].bit_length()==592884 and v['K0'].bit_length()<2*B
for m in range(1,20):
 for k in range(2,20):assert (8*m+9)*k*k>16 # 16*((m/2+9/16)k²−1)>0
print(json.dumps({'source_files_pinned':len(src)+len(extra_src)+1,'beta_bits':B,'K_bits':v['K0'].bit_length(),'K_less_than_min_q':True,'scope':'conditional standard-natural canonical-witness sign; no halt or general existence claim'},sort_keys=True,indent=2))
