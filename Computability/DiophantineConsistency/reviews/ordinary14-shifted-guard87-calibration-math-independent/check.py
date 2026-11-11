#!/usr/bin/env python3
"""Source, port, corrected strong-map and factor-three controls; no Lean."""
import gzip,hashlib,json,math,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-shifted-guard87-calibration'
def read(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b
final_readme=read(A/'README.md','005fd2c04cef4c997383bf373cc48acd326e829eb01ff4d30c218dadaf9f758a')
link_tail=b'\nIndependent mathematical review is recorded in\n`../../reviews/ordinary14-shifted-guard87-calibration-math-independent/`.\nA separate independent decoder review is recorded in\n`../../reviews/ordinary14-shifted-guard87-calibration-decoder-independent/`.\n'
assert final_readme.endswith(link_tail) and hashlib.sha256(final_readme[:-len(link_tail)]).hexdigest()=='84f69c32b78b26a13056c3ef27041c4086c7d0ec444e9d1d9cd12770153a1eee'
read(A/'check.py','142de39a368359171d5c37cb122fc22c91ac74450ac0523a1a2e46085fb346e7');read(A/'result.json','a8c6221eb05b6c86ec8db95d77d37cd77fc94a01c384ccf4ba411030318f8813')
files={'Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3','Compact44/FreeJMainOrientation.lean':'d02beb02122e682deef3e89c3dcb8e3e6aea31ddfbc4f320fe6af9a3df7f9a6b','Compact44/FreeJEarlyIndex.lean':'ab9b8e34903eff1e33e81b6a75438797eef1f2dab84595e23516b44de774ea3d','Compact44/FreeJPowerFinish.lean':'e4b2e84586b6232b9accc7775f094d4e1047453f1e8337f6241d39a6657d8816','ArithmeticPellPowerRecovery.lean':'636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390'}
src={n:read(D/'Lean/DiophantineConsistency'/n,h).decode() for n,h in files.items()}
ind=src['Compact44/P72Exact.lean'].split('theorem indices_ordinary',1)[1].split(' := by',1)[0]
for s in ('(hRμ : R + 1 < μ)','(hnmod : (2 * n) % μ = R + 1)','(hs\' : (i\' * c * c) * (i\' * c * c) + delta a = delta a * (f * f))'):assert s in ind
assert 'freej_first_factor_transport' in src['Compact44/FreeJPowerFinish.lean'] and 'theorem power_bound' in src['ArithmeticPellPowerRecovery.lean']
# Independent exact strong-premise controls, and scalar carrier scaling.
for a in range(0,25):
 Delta=(a+2)**2-1;c=1;f=2*Delta+1;i=2*Delta*(a+2)
 assert (i*c*c)**2==Delta*(f*f-1) and (i*c*c)**2+Delta==Delta*f*f
for q in range(3,180):
 for X in range(1,6):
  for y0 in range(1,4):
   Y=q**3*y0;H=3+4*Y*(X+1);g=math.gcd(H,q**5)
   assert g in (1,3) and q**5//g%q**4==0
   for w in (0,1,3):
    U=Y*q*q; m=X*Y*Y;W=4*X*q*y0*w
    assert 4*m*w==U*W
p=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';bind=json.loads(read(p/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'));other=json.loads(read(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'));v={}
for n,m in bind['ports'].items():
 assert other['ports'][n]['sha256_raw']==m['sha256_raw'] and other['ports'][n]['sha256_gzip']==m['sha256_gzip'];z=read(p/m['path'],m['sha256_gzip']);x=gzip.decompress(z);assert len(x)==m['raw_bytes'] and hashlib.sha256(x).hexdigest()==m['sha256_raw'];v[n]=int.from_bytes(x,'little')
assert v['beta']>=46 and 0<v['MC']<v['beta']<v['MF']<2*v['beta'] and v['K0']>=0
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check.py')],capture_output=True,check=True,timeout=120);assert r.stdout==(A/'result.json').read_bytes()
print(json.dumps({'i_prime':'i','mu':'q^4','factor_three_controls':177*5*3,'corrected_author_receipt_reproduced':True,'scope':'external standard-integer fact replay; no modified-graph Lean client or ancestry replay'},sort_keys=True,indent=2))
