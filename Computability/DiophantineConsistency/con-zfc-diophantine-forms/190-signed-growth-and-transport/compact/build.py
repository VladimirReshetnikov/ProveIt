#!/usr/bin/env python3
"""Rebuild the free-chart degree-190 polynomial from its exact parent."""
from pathlib import Path
import json,copy,collections,hashlib
ROOT=Path(__file__).resolve().parent
def build():
 parent=ROOT/'source/parent172.json'
 e=copy.deepcopy(json.loads(parent.read_text()))
 center=[
 ['pc_A','+','Am1',1],
 ['pc_kYprime','*','k','qY'],
 ['pc_e2','*','pc_kYprime','pc_kYprime'],
 ['pc_Yp1','+','qY',1],
 ['pc_kYYp1','*','pc_kYprime','pc_Yp1'],
 ['pc_sinner','-','V0kk','pc_kYYp1'],
 ['pc_S','*','pc_kYprime','pc_sinner'],
 ['pc_U2','*','U','U'],
 ['pc_theta','*','pc_U2','cTR'],
 ['pc_threeE','*',3,'Dtau'],
 ['pc_Zc','+','pc_threeE','pc_e2'],
 ['pc_thetaZc','*','pc_theta','pc_Zc'],
 ['pc_bmc','-','cTR','c'],
 ['pc_Rc','-','pc_thetaZc','pc_bmc'],
 ['pc_fourE','*',4,'Dtau'],
 ['pc_fourE2','*','pc_fourE','Dtau'],
 ['pc_S2','*','pc_S','pc_S'],
 ['pc_threeS2','*',3,'pc_S2'],
 ['pc_e22','*','pc_e2','pc_e2'],
 ['pc_sum1','+','pc_fourE2','pc_threeS2'],
 ['pc_Sc','+','pc_sum1','pc_e22'],
 ['pc_fourEV','*','pc_fourE','V'],
 ['pc_thetaSc','*','pc_theta','pc_Sc'],
 ['pc_Vdiff','-','pc_fourEV','pc_thetaSc'],
 ['pc_Apart','*','pc_A','pc_Vdiff'],
 ['pc_SRc','*','pc_S','pc_Rc'],
 ['pc_twoSRc','*',2,'pc_SRc'],
 ['pc_inner','+','pc_Apart','pc_twoSRc'],
 ['pc_Omega','*','U','pc_inner']]
 rows=[]
 for old in e['source']:
  r=list(old)
  if r[0]=='L':
   rows.extend(center)
   rows.append(['pc_b2','*','cTR','cTR'])
   rows.append(['L','*','UE','pc_b2'])
   continue
  if r[0]=='center':
   rows.append(['pc_n_minus_LB',r[1],r[2],r[3]])
   rows.append(['center','-','pc_n_minus_LB','pc_Omega'])
   continue
  if r[0]=='RG':r[3]='pc_G16'
  rows.append(r)
  if r[0]=='Dg':rows.append(['pc_G16','*',16,'Dg'])
 e['source']=rows
 e.update(name='positive10_degree190_ops119',operations=len(rows),operation_breakdown=dict(collections.Counter(r[1] for r in rows)),exact_degree=190,transport_weight='U*E*b^2',root_scale=4,polynomial_center='Omega in PROOF.md',proof='PROOF.md',mode='free_inverse_centered',normalization='lambda=q; Y=s; no auxiliary positive shift',parent={'path':'source/parent172.json','sha256':hashlib.sha256(parent.read_bytes()).hexdigest()},generation='Free chart, whole-product polynomial center, and a U*E*b^2 transport whose degree is low enough for the norm defect to dominate.')
 e['coefficient_binding']['path']='source/coefficients'
 return e
if __name__=='__main__':
 e=build();(ROOT/'equation.json').write_text(json.dumps(e,indent=2)+'\n');print(e['name'],e['operations'],e['operation_breakdown'])
