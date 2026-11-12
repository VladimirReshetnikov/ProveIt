from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path
p=P('research/ordinary13-natural89-r-replacement-model-draft')
files=[p/'Natural89RReplacement.lean.src',p/'Natural89MixedBridge.lean.src',p/'README.md',p/'check.py',p/'receipt.json',P('research/ordinary13-residue-root-switch-extraction-draft/ResidueRootSwitchExtract.lean.src'),P('research/ordinary13-residue-root-switch-model-draft/ResidueRootSwitchArithmetic.lean.src'),P('research/ordinary13-eta-natural-gap-rank-model-draft/EtaNaturalGapRank.lean.src'),P('research/ordinary13-eta-natural-X-positive-model-draft/EtaNaturalXPositive.lean.src'),P('research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src'),P('research/ordinary13-natural89-to-positive80-model-draft/Natural89Positive80Transport.lean.src'),P('research/ordinary13-natural89-direct-fy-model-draft/Natural89DirectFY.lean.src'),P('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json'),P('research/ordinary13-J88-to89-model-draft/J88To89Transport.lean.src'),P('research/ordinary13-gamma87-to88-model-draft/Gamma87To88Transport.lean.src'),P('research/ordinary13-w86-to87-model-draft/W86To87Transport.lean.src'),P('research/ordinary13-eta-unshift85-zero-map-model-draft/EtaUnshift85Transport.lean.src')]
s=[f.read_text() for f in files];g=json.loads(s[12]);rs={a[0]:a for a in g['source']}
assert len(rs)==85 and g['witnesses'][8]=='n_r'
def deps(n):
 if isinstance(n,int):return set()
 if n not in rs:return {n}
 return deps(rs[n][2])|deps(rs[n][3])
assert 'n_r' in deps('Z') and 'n_r' in deps('A0')
assert all('n_r' not in deps(n) for n in ('qm','ell','k','Bt','A1','Fa','Fs'))
for row in [['E','*','X','Y'],['kY','*','Y','k'],['ell','*','E','kY'],['g30','+','ell','k'],['g31','+','g30','n_r'],['folded_kBt','*','k','Bt'],['folded_g31','-','g31','folded_kBt'],['g32','*','qm','folded_g31'],['Z','-','g32','Bt'],['g38','*','Z','Z'],['g39','*','qm','qm'],['g40','*','ell','g30'],['g41','+',1,'g40'],['g42','*','g39','g41'],['A0','-','g38','g42'],['F0','+',1,'A0'],['F1','+',1,'A1'],['Fs','+',1,'g72'],['P01','*','F0','F1'],['P012','*','P01','Fa'],['P0123','*','P012','Fs'],['out','-','P0123',1]]: assert rs[row[0]]==row
# Associativity/commutativity certifies actual graph ell=(X*Y)*(Y*k)=m*k,
# and consequently ell*(ell+k) = m*(m+1)*k*k.
def add(a,b):
 c=a.copy()
 for key,n in b.items():c[key]=c.get(key,0)+n
 return {key:n for key,n in c.items() if n}
def mul(a,b):
 c={}
 for x,i in a.items():
  for y,j in b.items():
   z=tuple(a+b for a,b in zip(x,y));c[z]=c.get(z,0)+i*j
 return {key:n for key,n in c.items() if n}
one={(0,0,0):1};X={(1,0,0):1};Y={(0,1,0):1};k={(0,0,1):1};m=mul(mul(X,Y),Y);ell=mul(mul(X,Y),mul(Y,k))
assert ell==mul(m,k)
assert mul(ell,add(ell,k))==mul(mul(m,add(m,one)),mul(k,k))
for idx,pos in enumerate((0,12,6,9)):
 assert f'if i={pos} then v i+1 else v i' in s[13+idx]
 assert pos not in (3,8,11)
for i,needles in {0:['def putR','if i=8 then r else v i','theorem up_putR','theorem zero89_iff85','theorem prototype_update','EtaNaturalGapRankDraft.first_norm','ResidueRootSwitchExtractDraft.positive_replacement','Natural89Positive80TransportDraft.RReplacement K','w 3=v 3 ∧ w 11=v 11'],1:['replacement_of_cuts','Natural89DirectFYDraft.directFY K','Natural89RReplacementDraft.rReplacement K','(h80 : PolynomialBridge','ForcedEta K'],5:['theorem positive_replacement','(hb : 0<b) (hk : 2≤k)','ι ell*(ι ell+ι k)'],6:['theorem switch_from_zero','⟨2*tau'],7:['def firstRoot','theorem first_norm','m p v*k v'],8:['def k (v : Fin 13 → V) : V := v 9+v 10+1'],9:['theorem signed_norms'],10:['def RReplacement (K : ℕ)','w 3=v 3 ∧ w 11=v 11']}.items():
 for needle in needles: assert needle in s[i],needle
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in files},'first_root_rows_and_other_factor_dependencies_checked':True,'exact_ell_and_norm_polynomial_identities':True,'four_shift_positions_disjoint_from_r_f_y':True,'lean_executed':False,'status':'Unelaborated source audit; positive root extraction, maps, model providers and exact positive80 bridge require Lean validation.'},sort_keys=True,indent=2))
