from pathlib import Path
from hashlib import sha256
import ast,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-fixed-point-residue-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
C=Path('Lean/DiophantineConsistency/Compact44')
rowsrc=(C/'Compact943Data.lean').read_text();block=rowsrc.split('-- BEGIN PINNED ORDERED ROWS',1)[1].split('-- END PINNED ORDERED ROWS',1)[0]
rows=[tuple(map(int,m)) for m in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)',block)];assert len(rows)==943
slotsrc=(C/'CompactSymbolicKernel.lean').read_text();slots=ast.literal_eval(re.search(r'^def slots : List ℕ := (\[[^\n]+\])$',slotsrc,re.M).group(1));assert len(slots)==41 and max(slots)<4393
coef=(C/'CompactCoefficientMass.lean').read_text();assert 't.1 + 2^8*t.2.1 + 2^17*t.2.2.1 + 2^25*t.2.2.2 + 127*2^34' in coef
assert 'def selector (t : Nat × Nat × Nat × Nat) : Nat := 1 + 2^10 * (2^41 - value t)' in coef
kernel=(C/'CompactSymbolicKernelOpaque.lean').read_text()
for x in ('r^30+r^62+r^1100+r^2201','r^(4393-i.val)+r^(5495-i.val)','r^(4393-position i)+r^(5495-position i)','r^8807*r^42'):assert x in kernel
assert 'def rho : ℕ := 2^67' in slotsrc
assert 'range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032' in (C/'CompactConcreteMask.lean').read_text()
assert 'if j=special then B-4 else if j∈S then B-2 else B-1' in (C/'CompactListMask.lean').read_text()
high=(C/'CompactHighPopulation.lean').read_text()
for x in ('[4] ++ List.replicate 1012 0 ++ List.replicate 10 1 ++','List.replicate 42 0 ++ List.replicate 9 1 ++','List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1] ++','List.replicate 1096 0 ++ [mu] ++ List.replicate 1101 0 ++ [mu] ++','List.replicate 3296 0 ++ List.replicate 13 padding ++ [lastPadding,0]','def mu : ℕ := 2^51-2','def padding : ℕ := 2^65-1','def lastPadding : ℕ := 2^19-1'):assert x in high
assert 'def betaNat : ℕ := 2^(67*8807)-1' in (C/'CompactFixedBeta.lean').read_text()
assert '![β,K,L,β+H]' in (C/'CompactSymbolicPorts.lean').read_text()
N=67*8807;rho=pow(2,67,N);q=pow(2,N,N);beta=(q-1)%N
values=[a+2**8*b+2**17*c+2**25*d+127*2**34 for a,b,c,d in rows]
assert all(0<=x<=2**41 for x in values)
selectors=[1+2**10*(2**41-x) for x in values]
powrho=lambda e:pow(rho,e,N)
kp=(powrho(42)+sum(powrho(e) for e in (30,62,1100,2201))+
 sum(c*(powrho(4393-i)+powrho(5495-i)) for i,c in enumerate(selectors))+
 sum(2**(10+i)*(powrho(4393-pos)+powrho(5495-pos)) for i,pos in enumerate(slots)))%N
support=(set(range(943))|set(range(983,993))|set(range(1003,1012))|set(range(1013,1032))|{1063,1064,1095,2195,3296})-{1}
mc=sum((pow(2,67)-4 if j==1063 else pow(2,67)-2 if j in support else pow(2,67)-1)*powrho(j) for j in range(8807))%N
mu=2**51-2;padding=2**65-1;last=2**19-1
highdigits=[4]+[0]*1012+[1]*10+[0]*42+[1]*9+[0]*1121+[1]+[0]*1100+[1]+[0]*1096+[mu]+[0]*1101+[mu]+[0]*3296+[padding]*13+[last,0]
assert len(highdigits)==8807
hi=sum(v*powrho(j) for j,v in enumerate(highdigits))%N
mf=(beta+hi)%N
r=439547
# Graph rank after J=1, F=Kprime+2^r, alpha=beta-F:
# G=alpha+(q-F)*beta=q^2-1-qF.
A=((q*q-1-q*kp)*(q*q-1)+mc+q*mf)%N
B=(q*(q*q-1))%N
t=pow(2,r,N)
fixed=(A-B*t)%N
assert N==590069 and (q,beta,kp,mc,hi,mf)==(273473,273472,551654,428453,73733,347205)
assert (A,B,t,fixed)==(365222,460162,55048,r)
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'N':N,'q_mod_N':q,'beta_mod_N':beta,'Kprime_mod_N':kp,'MC_mod_N':mc,'MF_mod_N':mf,
 'rank_constant_mod_N':A,'rank_coefficient_mod_N':B,'two_pow_r_mod_N':t,
 'candidate_r':r,'derived_map_result':fixed,'derived_map_fixed_point_checked':True,
 'scope':'Exact recipe residues and derived rank-map evaluation only; full graph witness and zero require separate proof.',
 'lean_executed':False},sort_keys=True,indent=2))
