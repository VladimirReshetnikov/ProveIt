#!/usr/bin/env python3
"""Independent interval audit of the ACTUAL 38-billion-cross geometry.

No giant coefficient is materialized. Unlike enumerating toy source basis
vectors, this checks every actual native position by interval intersections.
"""
from pathlib import Path
import argparse
import json

ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source',type=Path,default=ROOT/'cross_constants.json')
parser.add_argument('--output',type=Path,default=ROOT/'cross_geometry_review.json')
args=parser.parse_args()
source=args.source
packet=json.loads(source.read_text())
g=packet['constants']['geometry']
a=439;k=38256607897
ell=36
p=max(0,(k-2*ell-9*a-4+1)//2)
jmax=5*a+4+p
m=2*ell+14*a+8+2*p
n=m+1
nd=n-k-5*a-4
estar=k+12*a
M=k+15*a+nd
Emax=27*M
H=51*M+3*a+1
T1=H+2*Emax+a+1
T2=T1+4*Emax+2
def next5(n):
 x=1;e=0
 while x<n:x*=5;e+=1
 return x,e
L,le=next5(T2+2*Emax+2)
U=4*(n+2)*(28*(k+5*a+4)+6)+8
bmin=max(ell*(jmax+1)+3,ell*(5*a+4)+U.bit_length()+1,4)
b,be=next5(bmin)
expected=dict(alphabet=a,crosses=k,ell=ell,padding=p,mu_top=jmax,m=m,
 native_positions=n,dummy_count=nd,dummy_start=estar,anchor_unit=M,emax=Emax,
 shift_H=H,T1=T1,T2=T2,cell_length=L,cell_length_power_five=le,
 radix_bits=b,radix_bits_power_five=be,radix_threshold=bmin,
 cell_bits=b*L,cell_bits_power_five=be+le,
 mask_population_MC=b*L-m-1,mask_population_MF=m+1)
assert expected==g
assert nd==1 and be==17 and le==19 and b*L==5**36

# Inclusive intervals representing ALL actual native positions.
E={'selectors':(0,k-1), 'prior':(k+10*a,k+11*a-1),
   'left':(k+8*a,k+9*a-1),'center':(k+7*a,k+8*a-1),
   'right':(k+6*a,k+7*a-1),'following':(k+4*a,k+5*a-1),
   'dummy':(estar,estar+nd-1),
   'anchor1':(M,M),'anchor3':(3*M,3*M),
   'anchor9':(9*M,9*M),'anchor27':(27*M,27*M)}
intervals=sorted(E.values())
assert all(x[1]<y[0] for x,y in zip(intervals,intervals[1:]))
assert sum(hi-lo+1 for lo,hi in intervals)==n
assert max(hi for name,(lo,hi) in E.items() if not name.startswith('anchor'))<M
assert estar+1<M

tests={'vprior':E['prior'],'vcenter':E['center'],
       'hleft':tuple(x+H for x in E['left']),
       'hcenter':tuple(x+H for x in E['center']),
       'anchor9':E['anchor9'],'anchor27':E['anchor27']}
short={'v':3*a,'h':H+a,'a8':8*M,'a24':24*M}
expected_current={('vprior','v'):'center',('vcenter','v'):'following',
 ('hleft','h'):'center',('hcenter','h'):'right',
 ('anchor9','a8'):'anchor1',('anchor27','a24'):'anchor3'}
expected_spatial={'hleft':'left','hcenter':'center'}
expected_temporal={'vprior':'prior','vcenter':'center',
                   'anchor9':'anchor9','anchor27':'anchor27'}
def intersects(a,b):return max(a[0],b[0])<=min(a[1],b[1])
audited=0
for tname,trange in tests.items():
 for sname,shift in short.items():
  pre=tuple(x-shift for x in trange)
  hits=[ename for ename,erange in E.items() if intersects(pre,erange)]
  want=expected_current.get((tname,sname))
  assert hits==([] if want is None else [want]),(tname,sname,hits,want)
  if want:assert pre==E[want]
  audited+=len(E)
 for shift,mapping in [(H,expected_spatial),(0,expected_temporal)]:
  pre=tuple(x-shift for x in trange)
  hits=[ename for ename,erange in E.items() if intersects(pre,erange)]
  want=mapping.get(tname)
  assert hits==([] if want is None else [want]),(tname,shift,hits,want)
  if want:assert pre==E[want]
  audited+=len(E)

# Exclude every high-band contribution to every non-clause test.
assert T1-max(hi for lo,hi in tests.values())>Emax
# At T1,T2 the short shifts and spatial/temporal copies are absent.
assert T1>max(short.values())+Emax
assert T1>H+Emax
assert T1>Emax
# Cross-band contributions require a difference bigger than all native spans.
assert T2-T1>2*Emax
# Supports, including the possible upper-dummy spill, cannot touch both clauses.
assert T2-T1>Emax+1 and L-(T2-T1)>Emax+1
assert T2+Emax<L

# Actual-mask occupied digit intervals are pairwise disjoint.
mask_intervals=list(tests.values())+[(T1,T1),(T2,T2)]
ordered=sorted(mask_intervals)
assert all(x[1]<y[0] for x,y in zip(ordered,ordered[1:]))
pc_mu=ell-1+jmax
assert m==2*pc_mu+4*a+2
assert (b*L-n)+(m+1)==b*L
assert min(lo for lo,hi in mask_intervals)>0
assert b>=4 and b>=ell*(jmax+1)+3

# Exact interval proof of the unique 18M native difference, including wrap.
hits=[]
for left,(llo,lhi) in E.items():
 for right,(rlo,rhi) in E.items():
  if rlo-lhi<=18*M<=rhi-llo:hits.append((left,right))
assert hits==[('anchor9','anchor27')],hits
assert L>54*M

# Unit identity: clause bands cancel modulo5 regardless of their coefficients.
assert (T2-T1)%4==2
unit=(2*(pow(2,3*a,5)+pow(2,H+a,5)+pow(2,8*M,5)+pow(2,24*M,5))-pow(2,H,5))%5
assert unit==3

result={'status':'PASS','independent_of_cross_constants_python':True,
 'actual_selector_count':k,'actual_native_position_count':n,
 'interval_intersection_checks':audited,
 'all_actual_positions_covered':True,'exact_scalar_geometry_match':True,
 'convolution_test_roles':True,'high_band_exclusion':True,
 'upper_dummy_spill_below_first_anchor':True,
 'all_rotation_clean_band_inequalities':True,
 'unique_anchor_difference':True,'mask_population_identity':True,
 'bit_length_B_minus_1_power_five':36,'mod5_unit':unit,
 'claim_scope':'exact actual-instance support/geometry check; not Pell/compiler formalization'}
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
