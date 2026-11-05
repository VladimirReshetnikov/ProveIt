#!/usr/bin/env python3
"""Independent bounded premise and theorem-interface review; no Lean."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def need(b,s):
    if not b:raise RuntimeError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=Path(__file__).resolve().parents[2];d=base/'research/p64-qcube72-partial-aux-exclusion';lean=base/'Lean/DiophantineConsistency'
pins={d/'README.md':'9a10d922e1dc1d502858e0bcd18ac89bce8e69af2e405d202bdbbf8bf8958357',
 d/'check.py':'79adae6832e3dbe4419318287ea6e042f704f5c900734f12e691b059d8c4a8d8',
 d/'result.json':'a92dbd562a0bb1f257312f3d3f4b387aedbf79ccc9caf2ea07996b3b74261aac',
 lean/'AdaptiveGap85GenericSignedHalfIndex.lean':'3f04ff3cf201f8657d3eb504b639fe6513256665a0e7cb001739068070ea1d60',
 lean/'ArithmeticPellFirstIndex.lean':'8cf79ed14f00f565accbfae0eb03ccacca597d06d12a509fecd6d3272e30f9ce',
 lean/'ArithmeticPellRecurrence.lean':'63ec2a49f8d7066dbd8647a663db4bbd7255abd3ca7c3cc0d4d7b3533a189b16',
 lean/'ArithmeticPellHalfIndex.lean':'7703193660d8ae98408d1ec3a83f6f8811927252e739bb7af18dbafb833a8877'}
for p,h in pins.items():need(sha(p)==h,'pin drift '+str(p))
r=subprocess.run([sys.executable,'-I','-S','-B',str(d/'check.py')],capture_output=True,check=True,timeout=20)
need(r.stdout==(d/'result.json').read_bytes() and not r.stderr,'author controls mismatch')
s=(lean/'AdaptiveGap85GenericSignedHalfIndex.lean').read_text()
for tok in ('theorem signed_half_index_of_facts (a c d f i t rp rn y m : V)',
 '(hc : 0<c) (hi : 0<i) (hf : 0<f) (hm : 0<m) (hy : 0<y)', '(hmy : ycoord m a=c)',
 '(hR : 0<absdiff rp rn) (hhalf : 2*absdiff rp rn<c)',
 '(hmain : d*d=1+delta a*c*c)', '(hstrong : (i*c*c)*(i*c*c)+delta a=delta a*(f*f))',
 '(hbig : (a+2)*delta a*delta a<c)',
 '(haux : let z := absdiff (f*f*(t*c+rn)) (f*f*rp+c)',
 '(i*c*c)*(i*c*c)*z*z+y*y=1+(i*c*c)*(i*c*c)*y*y)', 'm=absdiff rp rn'):
    need(tok in s,'theorem interface '+tok)
rec=(lean/'ArithmeticPellRecurrence.lean').read_text();first=(lean/'ArithmeticPellFirstIndex.lean').read_text();half=(lean/'ArithmeticPellHalfIndex.lean').read_text()
for tok in ('def delta (b : V) : V := (b+1)*(b+3)', 'run 0 b=⟪1,0⟫',
            'xcoord (time+1) b=(b+2)*xcoord time b+delta b*ycoord time b',
            'ycoord (time+1) b=xcoord time b+(b+2)*ycoord time b'):
    need(tok in rec,'Pell recurrence '+tok)
need('ycoord 6 a=32*(a+2)*delta a*delta a+32*(a+2)*delta a+6*(a+2)' in first,'sixth coefficient formula')
need('def absdiff (x y : V) : V := (x-y)+(y-x)' in half,'absolute difference definition')
a=189;n=a+2;D=(a+1)*(a+3);m=4020619;R=41;j=2446738
need(D==36480 and n*n-1==D and m>6 and m!=R and 27*(2*j)>2*R,'numeric signs and half bound')
def mul(x,y):return (x[0]*y[0]+D*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
v=(1,0)
for _ in range(6):v=mul(v,(n,1))
y6=32*n*D*D+32*n*D+6*n
need(v[1]==y6 and y6>n*D*D,'large-c premise')
# Finite sign controls verify the conversion from the integer residual to the
# theorem's absdiff form; the general identity is explained in README.
rng=random.Random(191041);both=set()
for _ in range(700):
 f,i,c,T,y=[rng.randrange(1,80) for _ in range(5)];rank=rng.randrange(1,90)
 left=f*f*T*c;right=f*f*rank+c;V=left-right;z=abs(V);I=i*c*c;both.add(V>0)
 need(V*V==z*z and (I*I*(V*V-y*y)+y*y==1)==(I*I*z*z+y*y==1+I*I*y*y),'absolute-value identity')
need(both=={False,True},'both signs not covered')
out={'status':'PASS_THEOREM_INTERFACE_AND_STANDARD_SPECIALIZATION_REVIEW','script_sha256':sha(__file__),
     'author_readme_sha256':pins[d/'README.md'],'theorem_source_sha256':pins[lean/'AdaptiveGap85GenericSignedHalfIndex.lean'],
     'recurrence_source_sha256':pins[lean/'ArithmeticPellRecurrence.lean'],'index':m,'rank':R,
     'y6_minus_bound':y6-n*D*D,'signed_controls':700,
     'scope':'Source-level standard-natural specialization of existing theorem, no new Lean client, unrestricted 72-zero exclusion, compact44 claim or full provider-ancestry audit.'}
print(json.dumps(out,indent=2,sort_keys=True))
