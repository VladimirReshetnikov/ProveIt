#!/usr/bin/env python3
"""Exact controls for the smallest A/even-m kernel-gcd complement."""
import hashlib,json,math,subprocess,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
prev=root/'research/ordinary13-parent-even-index-kernel-gcd-obstruction'
r=subprocess.run([sys.executable,'-I','-S','-B',str(prev/'check.py')],cwd=root,check=True,text=True,capture_output=True)
assert r.stdout==(prev/'receipt.json').read_text()
A=3;D=A*A-1;d=2;t=2;m=2;x,c=1,0
for _ in range(m):x,c=A*x+D*c,x+A*c
assert (D,d,t,c,x)==(8,2,2,6,17)
G=math.gcd(c*c,d*t);assert G==4 and c%G!=0
# A=2 has Δ=3 squarefree, so every gcd(c²,3) divides c.
for cc in range(1,500):assert cc%math.gcd(cc*cc,3)==0
f,yh=1,0;residues=[]
for h in range(1,7):
 f,yh=A*f+D*yh,f+A*yh
 residues.append(yh%9)
assert residues==[1,6,8,6,1,0]
I=D*yh;i=I//(c*c)
assert (f,yh,I,i)==(19601,6930,55440,1540)
assert I%(c*c)==0 and I*I==D*(f*f-1)
# A separate bounded scan confirms minimal f for this exact c and Δ.
for f0 in range(2,f):
 I0=math.isqrt(D*(f0*f0-1))
 assert I0*I0!=D*(f0*f0-1) or I0%(c*c)!=0
assert f%17==0 and I%17==3
coeff=(4*(I*I%17)-2)%17;v0=1;v1=(4*(I*I%17)-3)%17;seq=[]
for _ in range(4):seq.append(v0);v0,v1=v1,(coeff*v1-v0)%17
assert (v0,v1)==(1,(4*(I*I%17)-3)%17)
assert set(seq)=={1,16} and c%17 not in seq and (-c)%17 not in seq
print(json.dumps({'lexicographically_first_A_even_m_pair':[A,m],'Delta':D,
 'kernel_d':d,'square_part_t':t,'c':c,'gcd_c_squared_dt':G,
 'gcd_divides_c':False,'smallest_strong_f':f,'strong_I':I,'strong_i':i,
 'first_six_ordinates_mod9':residues,'toy_odd_aux_quotients_mod17':sorted(set(seq)),
 'all_strong_witnesses_excluded_by_general_integer_proof':True,
 'actual_graph_zero_or_existential_inequivalence_proved':False,'lean_executed':False},indent=2,sort_keys=True))
