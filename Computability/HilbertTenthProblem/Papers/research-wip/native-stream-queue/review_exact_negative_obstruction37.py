#!/usr/bin/env python3
"""Bounded data-only intake of Report 37; no archived programs execute."""
import argparse
import hashlib
import json
from pathlib import Path
import zipfile

ARCHIVE_NAME='Exact_Negative_Index_Obstruction_for_Positive_Diophantine_Interfaces_Package.zip'
ARCHIVE_SHA='018b960efd8069db99ec3eaa9b691cb2ca60edbc88932cc6e37cbf3562d169f9'
PREFIX='Research_Report37/evidence/'
WIP='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'
MEMBERS={
 'EXACT-OBSTRUCTION.md':'918b82b7666b4f5cbab5fd7a0b8298275ac62fe84f83261ef88ea863765d455f',
 'independent/INDEPENDENT-REVIEW.md':'3eae6bf05a24f603f9d30c02f83363d55accb9d38852fbc0fc5539f276feb130',
 'context/RAW-POSITIVE-REDUCTION.md':'0ae2f56e7db3177f3100198ae503c950d2f11d30d3d6d55d51f399dbdbeb48a9',
 'context/PRIOR-INDEPENDENT-REVIEW.md':'a82ee544ea93efae25ff8b4e60c3cbe01136d5db2273b82e8eee994f222b6656',
}
CURRENT={
 'complete74_negative_index_refinement.md':'a471a60a2b742e8d84ad9c19c333e6c7949e5da911c5b1149eded0854d3fbc99',
 'complete74_nonlinear_index_projection_scout.json':'ea982f9585eb4e16d756dfc33c73041e73e5e18a38ea37c2302d57c1fe104c92',
 'complete75_half_binomial_compiler.md':'68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 'complete75_positive_elimination.py':'70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749',
 'review_complete74_nonlinear_index_bootstrap.md':'4922eb2587fa1ecda313792ea0644c6da123b5ebdb86a0dbdfa02671d48ed1a8',
 'complete85_auxiliary_bezout_projection.json':'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc',
 'complete85_auxiliary_bezout_projection.md':'d8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b',
}
RAW_WITNESSES='C F Jrep W Z a alpha c d delta eta f ga h i j k kappa mu o phi q rho s tau w y_aux zeta zquot'.split()
POS_WITNESSES='Jrep F alpha zquot f h i j o s w tau eta zeta ga y_aux Z W delta phi rho'.split()
RAW_PAIRS=[['repunit','qm1'],['raw_bound','q'],['innerC','local_rhs_sum'],['restored_r','r_lhs'],['C','marked_rhs'],['L9','R9'],['c','R10a'],['k','R10b'],['a','R12'],['d','R14'],['L15','R15'],['ic22','R16'],['L17','P17'],['H17','aux_u_rhs'],['kappa','index_rhs'],['c','pell_gap'],['mu2','norm_rhs'],['mu','exponent_rhs']]
POS_PAIRS=[['raw_bound','q'],['innerC','local_rhs_sum'],['restored_r','r_lhs'],['L9','R9'],['L15','R15'],['ic22','R16'],['L17','P17'],['H17','aux_u_rhs'],['R10a','pell_gap'],['mu2','norm_rhs']]

def require(ok,message):
 if not ok:raise ValueError(message)
def digest(data):return hashlib.sha256(data).hexdigest()
def exact(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b

def pell(A,n,mod=None):
 D=A*A-1
 def times(a,b):
  x=a[0]*b[0]+D*a[1]*b[1];y=a[0]*b[1]+a[1]*b[0]
  return (x%mod,y%mod) if mod else (x,y)
 out=(1,0);base=(A,1)
 while n:
  if n&1:out=times(out,base)
  base=times(base,base);n//=2
 return out

def small_checks():
 aux=[];inputs=[];oddquot=[];packing=[]
 for A in (2,4,6,8):
  for p in (13,17):
   c=pell(A,p)[1];m=p*c*(1 if p%4==3 else 2);ell=p+2*m
   require(c%2==1 and pell(A,m,c*c)[1]==0 and ell%4==1,'auxiliary divisibility/parity')
   require(ell%c==p%c,'auxiliary target congruence')
   aux.append([A,p,c,m,ell])
  for u in (3,5,7):
   for e in (u,u*A):
    mu,kappa=pell(A,e);D=A*A-1;H=4*(A-2)+3
    require((kappa-u)%D==0 and kappa>u,'positive input delta')
    require((mu-(A-2)*kappa-pow(2,e,H))%H==0,'input projection')
    inputs.append([A,u,e])
  # The integer recurrence evaluates Q_h(z)=chi_s(2h+1)/s at z=s².
  z=1-A*A;previous,current=1,4*z-3
  for h in range(9):
   value=1 if h==0 else current
   require(value==(-1)**h*pell(A,2*h+1)[1],'odd quotient specialization')
   oddquot.append([A,h])
   if h:previous,current=current,(4*z-2)*current-previous
 for q in (16,32):
  for F in (q+1,q+3):
   for Z in (2,q-2):
    for M in (q+1,2*q+3):
     Q=q*q-1;p=(Z+q*F-q*q)*Q-M
     require(p>0 and (p+M)%Q==0,'negative packing')
     N=(p+M)//Q;restoredZ=N%q;restoredF=q+(N-restoredZ)//q
     require((restoredZ,restoredF)==(Z,F),'unique packing recovery')
     packing.append([q,F,Z,M,p])
 return {'auxiliary_modular_cases':len(aux),'input_projection_cases':len(inputs),
  'odd_quotient_specializations':len(oddquot),'packing_recoveries':len(packing),
  'cases_sha256':digest(json.dumps([aux,inputs,oddquot,packing],separators=(',',':')).encode()),
  'scope':'Small algebra-only cases, not valid compiler exports or full negative zeros; no full large auxiliary tuple materialized.'}

def inventory(packet,witnesses,pairs):
 require(packet['witnesses']==witnesses and packet['comparisons']==pairs,'literal witness/comparison inventory')
 rows=packet['source'];d={r[0]:r for r in rows};raw=packet['mode']=='raw30'
 c='c' if raw else 'R10a';k='k' if raw else 'R10b'
 required=[['n2','*','Lbig','q'],['wn2','*','w','n2'],['sn2','*','s','n2'],
 ['marked_rhs','+','Z','W'],['hpm1','*','h','UM'],['index_partial','-',k,'hpm1'],
 ['restored_r','-','index_partial',1],['H17','-','jc','restored_r'],
 ['jc','*','j',c],['aux_u_rhs','-','of',c],['ic2','*','i','c2'],
 ['ic22','*','ic2','ic2'],['f_square_minus_one','-','L16',1],['R16','*','A','f_square_minus_one'],
 ['local_rhs_sum','+','F','local_rhs'],['r_lhs','+','rproduct','mask']]
 require(all(d.get(r[0])==r for r in required),'source-aware prerequisites')
 tail=[]
 for i,(a,b) in enumerate(pairs):
  tail.extend([[f'residual_{i}','-',a,b],[f'square_{i}','*',f'residual_{i}',f'residual_{i}']])
 for i in range(1,len(pairs)):
  tail.append([f'sum_{i}','+','square_0' if i==1 else f'sum_{i-1}',f'square_{i}'])
 require(packet['polynomial_source']==rows+tail and packet['output']==f'sum_{len(pairs)-1}','complete SOS finalizer')
 return {'mode':packet['mode'],'positive_witnesses':len(witnesses),'comparisons':len(pairs),
  'full_gates':len(rows+tail),'finalizer_gates':len(tail),'source_sha256':digest(json.dumps(rows,separators=(',',':')).encode())}

def verify(repo,archive):
 require(digest(archive.read_bytes())==ARCHIVE_SHA,'archive pin')
 current={}
 for name,pin in CURRENT.items():
  data=(repo/WIP/name).read_bytes();require(digest(data)==pin,'current pin '+name);current[name]=data
 with zipfile.ZipFile(archive) as z:
  require(len(z.namelist())==len(set(z.namelist())),'duplicate members')
  for name,pin in MEMBERS.items():require(digest(z.read(PREFIX+name))==pin,'member pin '+name)
  matched=[]
  for name in list(CURRENT)[:5]:
   require(z.read(PREFIX+'sources/'+name)==current[name],'current/archive full bytes '+name);matched.append(name)
 receipt=json.loads(current['complete74_nonlinear_index_projection_scout.json'])
 forms={f['packet']['mode']:f['packet'] for f in receipt['forms']}
 inv=[inventory(forms['raw30'],RAW_WITNESSES,RAW_PAIRS),inventory(forms['positive22'],POS_WITNESSES,POS_PAIRS)]
 p85=json.loads(current['complete85_auxiliary_bezout_projection.json'])['packet'];d={r[0]:r for r in p85['source']}
 required=[['wn2','*','w','q'],['q_minus_F','-','q','F'],['q_minus_FZ','-','q_minus_F','Z'],
 ['C_after_alpha','-','q_minus_FZ','alpha'],['marked_rhs','-','C_after_alpha','scaled_t'],
 ['kinner','+','Kconstant','w'],['innerC','*','kinner','marked_rhs'],
 ['transport_partial','+','innerC','q_minus_F'],['local_rhs','*','transport_quotient','repunit'],
 ['norm_transport','-','transport_partial','local_rhs'],['norm_index','-','index_difference','r_lhs']]
 require(all(d.get(r[0])==r for r in required),'actual85 separation')
 return {'status':'PASS','source_sha256':digest(Path(__file__).read_bytes()),'archive_sha256':ARCHIVE_SHA,
  'member_pins':MEMBERS,'current_pins':CURRENT,'current_archive_byte_matches':matched,
  'literal_source_inventories':inv,'small_independent_checks':small_checks(),
  'normalized85_boundary':'Report37 negative branch requires F>=q; actual85 unit transport and marked-word definition imply F+Z<q.',
  'theorem_scope':'Exact full-negative-zero criterion with only q,w unbounded, not existence or exclusion. Raw29/positive21 remain unresolved. No asymmetric transfer, new loader, universal bound, archive execution, or full negative compiler zero.'}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--archive',type=Path)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 a=ap.parse_args();archive=a.archive or a.repo/'docs/incoming'/ARCHIVE_NAME;r=verify(a.repo,archive)
 text=json.dumps(r,indent=2,sort_keys=True)+'\n';require(exact(r,json.loads(text)),'typed roundtrip')
 if a.output:a.output.write_text(text)
 else:require(exact(r,json.loads(a.expect.read_text())),'saved receipt')
 print(json.dumps({'status':'PASS','source_modes':2,'source_matches':5,'checks':r['small_independent_checks']},sort_keys=True))
if __name__=='__main__':main()
