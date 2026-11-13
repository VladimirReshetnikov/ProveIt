#!/usr/bin/env python3
"""Guarded exact-input MPFR interval exclusion; no Pell ordinate expansion."""
import ctypes,hashlib,io,json,resource,runpy,sys
from contextlib import redirect_stdout
from pathlib import Path
# Hard limits precede library allocation. An outer wall-clock timeout is also required.
LIMIT=768*1024*1024
resource.setrlimit(resource.RLIMIT_AS,(LIMIT,LIMIT))
resource.setrlimit(resource.RLIMIT_CPU,(45,45))
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2]; here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
prev=root/'research/ordinary13-f-unshift-fixed-small-power-w-gcd'
buf=io.StringIO()
with redirect_stdout(buf):data=runpy.run_path(str(prev/'check.py'))
assert buf.getvalue()==(prev/'receipt.json').read_text()
beta=data['beta'];Kp=data['kp'];N=67*8807;q=1<<N
assert beta==q-1 and 0<Kp<1<<(67*5496)
t=(beta-1)//2;w=t-Kp;assert w>0
base=root/'Lean/DiophantineConsistency/Compact44'
masksrc=(base/'CompactConcreteMask.lean').read_text()
assert 'range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032' in masksrc
assert '{1063,1064,1095,2195,3296}) \\ {1}' in masksrc
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in (base/'CompactListMask.lean').read_text()
hsrc=(base/'CompactHighPopulation.lean').read_text()
for tok in ('def mu : ℕ := 2^51-2','def padding : ℕ := 2^65-1',
 '[4] ++ List.replicate 1012 0 ++ List.replicate 10 1',
 'List.replicate 42 0 ++ List.replicate 9 1',
 'List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1]',
 'List.replicate 1096 0 ++ [mu] ++ List.replicate 1101 0 ++ [mu]',
 'List.replicate 3296 0 ++ List.replicate 13 padding ++ [lastPadding,0]',
 'def lastPadding : ℕ := 2^19-1'):
 assert tok in hsrc,tok
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
MC=beta-sum(1<<(67*j) for j in support)-2*(1<<(67*1063))
mu=2**51-2; padding=2**65-1;last=2**19-1
hd=[4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+[0]*1096+[mu]+[0]*1101+[mu]+[0]*3296+[padding]*13+[last,0]
assert len(hd)==8807
high=sum(x<<(67*j) for j,x in enumerate(hd) if x);MF=beta+high
assert 0<=MC<beta and beta<=MF<2*beta and MC%2==0
# R=(beta^2+2)(q^2-1)+MC+q*MF; use shifts to avoid giant multiplication.
G=(1<<(2*N))-(1<<(N+1))+3
R=(G<<(2*N))-G+MC+(MF<<N)
assert R>0 and R%2==1;n=(R+1)//2
X=w<<N;Y=1<<(3*N);M=w<<(7*N);Af=2*M+1
A=(Y*(X+1))+2
assert 0<n<Af and 2*n<A and Y>=8 and X>=1 and n.bit_length()<=4*N+2
p=n.bit_length()+192
assert p<2400000
class Mp(ctypes.Structure):
 _fields_=[('prec',ctypes.c_long),('sign',ctypes.c_int),('exp',ctypes.c_long),('data',ctypes.POINTER(ctypes.c_ulong))]
P=ctypes.POINTER(Mp);mp=ctypes.CDLL('libmpfr.so.6')
mp.mpfr_get_version.restype=ctypes.c_char_p
mp.mpfr_init2.argtypes=[P,ctypes.c_long];mp.mpfr_clear.argtypes=[P]
mp.mpfr_set_str.argtypes=[P,ctypes.c_char_p,ctypes.c_int,ctypes.c_int];mp.mpfr_set_str.restype=ctypes.c_int
for name in ('mpfr_log','mpfr_ceil','mpfr_floor'):
 getattr(mp,name).argtypes=[P,P,ctypes.c_int] if name=='mpfr_log' else [P,P]
for name in ('mpfr_mul','mpfr_div','mpfr_sub'):
 getattr(mp,name).argtypes=[P,P,P,ctypes.c_int]
for name in ('mpfr_add_ui','mpfr_sub_ui'):
 getattr(mp,name).argtypes=[P,P,ctypes.c_ulong,ctypes.c_int]
mp.mpfr_mul_2ui.argtypes=[P,P,ctypes.c_ulong,ctypes.c_int]
mp.mpfr_cmp.argtypes=[P,P];mp.mpfr_cmp.restype=ctypes.c_int
mp.mpfr_cmp_ui.argtypes=[P,ctypes.c_ulong];mp.mpfr_cmp_ui.restype=ctypes.c_int
RNDU=2;RNDD=3
items=[]
def new():
 x=Mp();mp.mpfr_init2(ctypes.byref(x),p);items.append(x);return x
def ptr(x):return ctypes.byref(x)
def number(v,mode):
 x=new(); assert mp.mpfr_set_str(ptr(x),format(v,'x').encode(),16,mode)==0;return x
def logarithm(v,mode):
 x=number(v,mode);y=new();mp.mpfr_log(ptr(y),ptr(x),mode);return y
try:
 ne=number(n,RNDD) # exact: p > bit length of n.
 laf_lo=logarithm(2*Af,RNDD);laf_hi=logarithm(2*Af,RNDU)
 la_lo=logarithm(2*A,RNDD);la_hi=logarithm(2*A,RNDU)
 numlo,numhi,lo,hi=new(),new(),new(),new()
 mp.mpfr_mul(ptr(numlo),ptr(ne),ptr(laf_lo),RNDD);mp.mpfr_sub_ui(ptr(numlo),ptr(numlo),2,RNDD)
 mp.mpfr_mul(ptr(numhi),ptr(ne),ptr(laf_hi),RNDU);mp.mpfr_add_ui(ptr(numhi),ptr(numhi),5,RNDU)
 assert mp.mpfr_cmp_ui(ptr(numlo),0)>0 and mp.mpfr_cmp_ui(ptr(la_lo),0)>0
 mp.mpfr_div(ptr(lo),ptr(numlo),ptr(la_hi),RNDD)
 mp.mpfr_div(ptr(hi),ptr(numhi),ptr(la_lo),RNDU)
 ceiling,floor=new(),new();mp.mpfr_ceil(ptr(ceiling),ptr(lo));mp.mpfr_floor(ptr(floor),ptr(hi))
 no_integer=mp.mpfr_cmp(ptr(ceiling),ptr(floor))>0
 assert mp.mpfr_cmp(ptr(lo),ptr(hi))<=0
 # Confirm enough precision for exact floor/ceil and expose a safe gap bound.
 two_n_plus=number(2*n+2,RNDU);assert mp.mpfr_cmp(ptr(hi),ptr(two_n_plus))<0
 gap=new();scaled=new();gap_gt_2m20=False
 if no_integer:
  mp.mpfr_sub(ptr(gap),ptr(ceiling),ptr(hi),RNDD)
  mp.mpfr_mul_2ui(ptr(scaled),ptr(gap),20,RNDD)
  gap_gt_2m20=mp.mpfr_cmp_ui(ptr(scaled),1)>0
 print(json.dumps({'mpfr_version':mp.mpfr_get_version().decode(),'rounding':'lower RNDD, upper RNDU',
  'precision_bits':p,'first_index_bits':n.bit_length(),'main_multiplier_bits':A.bit_length(),
  'first_multiplier_bits':Af.bit_length(),'exact_n_less_than_Af_and_2n_less_than_A':True,
  'outer_log_envelope':'(n*log(2Af)-2)/log(2A) < m < (n*log(2Af)+5)/log(2A)',
  'closed_interval_contains_no_integer':no_integer,'gap_to_next_integer_gt_2^-20':gap_gt_2m20,
  'compact_partial_family_excluded':no_integer,
  'global_graph_zero_or_parent_equivalence_proved':False,'fixed_Pell_coordinates_expanded':False,
  'address_space_cap_MiB':768,'cpu_cap_seconds':45,'lean_executed':False},indent=2,sort_keys=True))
finally:
 for x in items:mp.mpfr_clear(ptr(x))
