from pathlib import Path
import hashlib,json,random
p=Path(__file__).resolve().parent;s=(p/'ParentQuotientFacts.lean').read_text()
for t in ('scaled_quotient','magnitude_mod z Q','unit_certificate_cancel','magnitude_mod z b','dvd_magnitude_of_mod','b∣magnitude (Bp,Bn)','let L : V := 3+3*b+b*b+k*Q'):assert t in s
rng=random.Random(131388)
for _ in range(5000):
 b,Y,P,r,k,Bp,Bn=[rng.randrange(1,20) for _ in range(7)]
 q=1+b;Q=q**3;M=Q*b;W=1+k*b;L=3+3*b+b*b+k*Q
 zp=M*(P+r)+b*Y+Bn*W*Q;zn=Bp*W*Q
 assert W*Q==1+b*L
 if abs(zp-zn)%M==0:
  assert Y%Q==0 and abs(Bp-Bn)%b==0
print(json.dumps({'signed_modular_controls':5000,'lean_run':False,'source_sha256':hashlib.sha256((p/'ParentQuotientFacts.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
