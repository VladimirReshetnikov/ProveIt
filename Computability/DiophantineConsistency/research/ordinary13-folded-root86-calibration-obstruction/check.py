#!/usr/bin/env python3
"""Source pins, compact44 residues, and finite arithmetic controls; no Lean."""
import gzip,hashlib,json,math
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h;return b
base='Lean/DiophantineConsistency/Compact44/'
hashes={'FreeJFirstTransport.lean':'3d806de318b1c798e8b2a31ca14e790a14d09b3996acf9c4c3346d3fc42c2029','FreeJRootBinding.lean':'7e395c9461414fef818fe1319aad1a31bbd62536ea143c66c8e8134c1ed00b01','FreeJSaturationClient.lean':'714988e8e7431d8dc45f3c5991ae5aaa0373812b34048eac74917209be8110ca','FreeJPowerProjection.lean':'fee95da196452c374b5d6aeaf2b3bb330e8d690224ad8dab523760df79da2749','FreeJPowerFinish.lean':'e4b2e84586b6232b9accc7775f094d4e1047453f1e8337f6241d39a6657d8816','CompactLeafFactsLiteral.lean':'c9bf7bebe4bdc947ee8232a96e4cdf798ebacbc7e635256ac41dcd381410a3c0','P72Window.lean':'7d1f669dd489045e23ffcbc6bf19049d9787ccd5cc766e77985421fd9255033d'}
t={n:pin(base+n,h).decode() for n,h in hashes.items()}
assert 'M*(ell+k+v 7)' in t['FreeJFirstTransport.lean'] and 'have hBt : Bn<Bp' in t['FreeJFirstTransport.lean'] and 'have hgap : v 1+v 2<q' in t['FreeJFirstTransport.lean']
for n in ('FreeJSaturationClient.lean','FreeJPowerProjection.lean','FreeJPowerFinish.lean','CompactLeafFactsLiteral.lean'):assert 'freej_first_factor_transport' in t[n]
assert '(hq : q = F + (C + α))' in t['P72Window.lean']
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';b=json.loads(pin(str((p72/'ACTIVE_BINDING.json').relative_to(D)),'6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'));b115=json.loads(pin('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'));v={}
for n,m in b['ports'].items():
 assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=(p72/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];raw=gzip.decompress(z);assert len(raw)==m['raw_bytes'] and hashlib.sha256(raw).hexdigest()==m['sha256_raw'];v[n]=int.from_bytes(raw,'little')
beta,K,MC,MF=(v[n] for n in ('beta','K0','MC','MF'));B=beta.bit_length();assert B==590069 and beta==(1<<B)-1 and min(K,MC,MF)>0 and beta%2==1
s=((1-K)*((beta+1)//2))%beta or beta; assert 1<=s<=beta and (2*s+K-1)%beta==0
for Y in range(9,80):
 X=2*Y-2;m=X*Y*Y;P=2*m+1;k=4*P;tau=2*P*P-1;ell=m*k;a=X*Y+Y;A=a+2;H=4*a+3;c=4*A*A-1;eta=c-Y*k;zeta=k-eta;d=4*A**3-3*A
 assert eta==36*Y*Y-20*Y+15 and zeta==16*Y**3-52*Y*Y+20*Y-11 and eta>0 and zeta>0
 assert tau*tau==1+m*(m+1)*k*k and d*d==1+(A*A-1)*c*c
 assert d-a*c==8+H*(2*a+6) and (H-(8*Y+36)*(Y-5))==183
print(json.dumps({'beta_bits':B,'K_bits':K.bit_length(),'s_bits':s.bit_length(),'s_sha256':hashlib.sha256(s.to_bytes((s.bit_length()+7)//8,'big')).hexdigest(),'scalar_congruence':True,'small_polynomial_controls':71,'scope':'actual compact44 first-zero and bare Pell control, A1 necessarily fails; source dependency only, no Lean or full zero'},sort_keys=True,indent=2))
