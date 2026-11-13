#!/usr/bin/env python3
import ctypes,hashlib,io,json,math,re,resource,runpy,signal,sys
from contextlib import redirect_stdout
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
resource.setrlimit(resource.RLIMIT_AS,(768*1024*1024,768*1024*1024))
resource.setrlimit(resource.RLIMIT_CPU,(40,40))
resource.setrlimit(resource.RLIMIT_CORE,(0,0))
signal.alarm(50)
D=Path('research/ordinary9-compact-partial-log-interval-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==h,p
base=Path('Lean/DiophantineConsistency/Compact44')
s=(base/'Compact943Data.lean').read_text().split('-- BEGIN PINNED ORDERED ROWS')[1].split('-- END PINNED ORDERED ROWS')[0]
rows=[tuple(map(int,x)) for x in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)',s)]
s=(base/'CompactSymbolicKernel.lean').read_text()
slots=list(map(int,re.search(r'def slots : List ℕ := \[([^]]+)\]',s).group(1).split(',')))
assert len(rows)==943 and len(slots)==41
assert 'def betaNat : ℕ := 2^(67*8807)-1' in (base/'CompactFixedBeta.lean').read_text()
N=67*8807;q=1<<N;beta=q-1
kp=sum(1<<(67*j) for j in (30,62,1100,2201,42))
for j,(a,b,c,d) in enumerate(rows):
 v=a+2**8*b+2**17*c+2**25*d+127*2**34
 assert 0<v<2**41
 selector=1+2**10*(2**41-v)
 kp+=selector*((1<<(67*(4393-j)))+(1<<(67*(5495-j))))
for j,slot in enumerate(slots):kp+=(1<<(10+j))*((1<<(67*(4393-slot)))+(1<<(67*(5495-slot))))
assert 0<kp<1<<(67*5496)
pre=Path("research/ordinary13-f-unshift-fixed-small-power-w-gcd"); capture=io.StringIO()
with redirect_stdout(capture): direct=runpy.run_path(str(pre/"check.py"))
assert capture.getvalue()==(pre/"receipt.json").read_text() and kp==direct["kp"] and beta==direct["beta"]
masksrc=(base/'CompactConcreteMask.lean').read_text();listsrc=(base/'CompactListMask.lean').read_text();highsrc=(base/'CompactHighPopulation.lean').read_text()
assert 'range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032' in masksrc
assert '{1063,1064,1095,2195,3296}) \\ {1}' in masksrc
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in listsrc
for x in ('def mu : ℕ := 2^51-2','def padding : ℕ := 2^65-1','def lastPadding : ℕ := 2^19-1','[4] ++ List.replicate 1012 0 ++ List.replicate 10 1','List.replicate 42 0 ++ List.replicate 9 1','List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1]','List.replicate 1096 0 ++ [mu] ++ List.replicate 1101 0 ++ [mu]','List.replicate 3296 0 ++ List.replicate 13 padding ++ [lastPadding,0]'):assert x in highsrc
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
MC=beta-sum(1<<(67*j) for j in support)-2*(1<<(67*1063))
digits=[4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+[0]*1096+[2**51-2]+[0]*1101+[2**51-2]+[0]*3296+[2**65-1]*13+[2**19-1,0]
assert len(digits)==8807
MF=beta+sum(digit<<(67*j) for j,digit in enumerate(digits) if digit)
assert 0<=MC<beta and beta<=MF<2*beta and MC%2==0
R=(beta*beta+2)*(q*q-1)+MC+q*MF
assert R>0 and R%2==1
n=(R+1)//2;w=(q-2)//2-kp;assert w>0
X=q*w;Y=q**3;A=Y*(X+1)+2;Af=2*X*Y**2+1
assert n<Af and 2*n<A and X>=1 and Y>=8
precision=n.bit_length()+144
assert precision<2400000
class F(ctypes.Structure):_fields_=[('precision',ctypes.c_long),('sign',ctypes.c_int),('exp',ctypes.c_long),('limbs',ctypes.POINTER(ctypes.c_ulong))]
Ptr=ctypes.POINTER(F);lib=ctypes.CDLL('libmpfr.so.6')
lib.mpfr_get_version.restype=ctypes.c_char_p
lib.mpfr_init2.argtypes=[Ptr,ctypes.c_long];lib.mpfr_clear.argtypes=[Ptr]
lib.mpfr_set_str.argtypes=[Ptr,ctypes.c_char_p,ctypes.c_int,ctypes.c_int];lib.mpfr_set_str.restype=ctypes.c_int
lib.mpfr_log.argtypes=[Ptr,Ptr,ctypes.c_int]
for s in ('mul','div') :getattr(lib,'mpfr_'+s).argtypes=[Ptr,Ptr,Ptr,ctypes.c_int]
for s in ('add_ui','sub_ui'):getattr(lib,'mpfr_'+s).argtypes=[Ptr,Ptr,ctypes.c_ulong,ctypes.c_int]
lib.mpfr_ceil.argtypes=[Ptr,Ptr];lib.mpfr_floor.argtypes=[Ptr,Ptr];lib.mpfr_cmp.argtypes=[Ptr,Ptr];lib.mpfr_cmp.restype=ctypes.c_int;lib.mpfr_cmp_ui.argtypes=[Ptr,ctypes.c_ulong];lib.mpfr_cmp_ui.restype=ctypes.c_int
objs=[]
def mk():
 z=F();lib.mpfr_init2(ctypes.byref(z),precision);objs.append(z);return z
def p(x):return ctypes.byref(x)
def val(x,r):
 z=mk();assert lib.mpfr_set_str(p(z),format(x,'x').encode(),16,r)==0;return z
def lg(x,r):
 a=val(x,r);z=mk();lib.mpfr_log(p(z),p(a),r);return z
DOWN=3;UP=2
try:
 integer_n=val(n,DOWN)
 first_lower=lg(2*Af,DOWN);first_upper=lg(2*Af,UP)
 main_lower=lg(2*A,DOWN);main_upper=lg(2*A,UP)
 numerlo=mk();numerhi=mk();lo=mk();hi=mk();integerlo=mk();integerhi=mk()
 lib.mpfr_mul(p(numerlo),p(integer_n),p(first_lower),DOWN);lib.mpfr_sub_ui(p(numerlo),p(numerlo),1,DOWN)
 lib.mpfr_mul(p(numerhi),p(integer_n),p(first_upper),UP);lib.mpfr_add_ui(p(numerhi),p(numerhi),3,UP)
 assert lib.mpfr_cmp_ui(p(numerlo),0)>0 and lib.mpfr_cmp_ui(p(main_lower),0)>0
 lib.mpfr_div(p(lo),p(numerlo),p(main_upper),DOWN);lib.mpfr_div(p(hi),p(numerhi),p(main_lower),UP)
 assert lib.mpfr_cmp(p(lo),p(hi))<=0
 bound=val(2*n+2,UP);assert lib.mpfr_cmp(p(hi),p(bound))<0
 lib.mpfr_ceil(p(integerlo),p(lo));lib.mpfr_floor(p(integerhi),p(hi))
 excluded=lib.mpfr_cmp(p(integerlo),p(integerhi))>0
 print(json.dumps({'precision_bits':precision,'first_index_bits':n.bit_length(),'outer_envelope':'(n log(2Af)-1)/log(2A) < m < (n log(2Af)+3)/log(2A)','mpfr_version':lib.mpfr_get_version().decode(),'no_integer_in_closed_outer_interval':excluded,'conditional_partial_family_excluded':excluded,'all_inputs_compact_source_reconstructed':True,'full_graph_equivalence_or_zero_proved':False,'lean_executed':False,'cpu_cap_seconds':40,'address_space_cap_MiB':768},sort_keys=True,indent=2))
finally:
 for z in objs:lib.mpfr_clear(p(z))
