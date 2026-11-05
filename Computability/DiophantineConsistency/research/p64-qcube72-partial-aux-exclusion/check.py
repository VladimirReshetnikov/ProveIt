#!/usr/bin/env python3
"""Bounded premise and signed-square controls; no Lean or huge Pell expansion."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B without optimization')
r=Path(__file__).resolve().parents[2]
pins={r/'research/p64-qcube72-compact-window-partial-obstruction/README.md':'174157fba427260500f36221798d5d629ea196125af30fa235e19294eee5f63f',r/'research/p64-qcube72-compact-window-partial-obstruction/check.py':'f3a6ba97dd648f46fe7723948e849bdd1c16e94b7bb976db15a3c129c2f3bb57',r/'Lean/DiophantineConsistency/AdaptiveGap85GenericSignedHalfIndex.lean':'3f04ff3cf201f8657d3eb504b639fe6513256665a0e7cb001739068070ea1d60',r/'Lean/DiophantineConsistency/ArithmeticPellFirstIndex.lean':'8cf79ed14f00f565accbfae0eb03ccacca597d06d12a509fecd6d3272e30f9ce'}
for p,h in pins.items():
 if hashlib.sha256(p.read_bytes()).hexdigest()!=h:raise RuntimeError('pin mismatch '+str(p))
p=r/'research/p64-qcube72-compact-window-partial-obstruction/check.py'
r1=json.loads(subprocess.run([sys.executable,'-I','-S','-B',str(p)],capture_output=True,text=True,timeout=20,check=True).stdout)
if r1['status']!='PASS_BOUNDED_PREMISES' or (r1['q'],r1['R'],r1['carrier_mod_q'])!=(3,41,2):raise RuntimeError('premise mismatch')
a,D,m,R,q=189,36480,4020619,41,3;n=a+2
ysix=32*n*D*D+32*n*D+6*n;bound=n*D*D
if not (D==(a+1)*(a+3) and m>=6 and m!=R and ysix>bound and 27*(2*2446738)>2*R and 24<=R and R+q**3+q+1<=q**4):raise RuntimeError('bounds mismatch')
rng=random.Random(720141)
for _ in range(500):
 f,i,c,T,y=[rng.randrange(1,20) for _ in range(5)];rp=rng.randrange(1,30)
 I=i*c*c;left=f*f*T*c;right=f*f*rp+c;V=left-right;z=abs(left-right)
 if z*z!=V*V or (I*I*(V*V-y*y)+y*y==1)!=(I*I*z*z+y*y==1+I*I*y*y):raise RuntimeError('signed-square identity')
print(json.dumps({'status':'PASS_FINITE_PREMISES','main_index':m,'rank':R,'rank_window':f'{R}+{q}³+{q}+1 ≤ {q}⁴','y6_minus_bound_positive':ysix-bound,'signed_square_cases':500,'scope':'Checks finite premises and algebra controls; the universal exclusion follows by the referenced half-index theorem and the accompanying argument, not a new Lean check.'},sort_keys=True))
