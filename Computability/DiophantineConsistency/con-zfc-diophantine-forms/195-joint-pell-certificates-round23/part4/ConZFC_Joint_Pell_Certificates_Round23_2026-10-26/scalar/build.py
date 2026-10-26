#!/usr/bin/env python3
"""Build two free-chart quotient centers at the coherent Start-only4127 tuple."""
from pathlib import Path
from collections import Counter
import argparse,copy,hashlib,json
ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'inherited_positive10/start4127_positive10_degree214_ops87.json'

def build(mode):
 g=json.loads(PARENT.read_text()); rows=[]
 common=[['pc_A','+','Am1',1],['pc_kN','*','k','qY'],['pc_Np1','+','qY',1],['pc_kNNp1','*','pc_kN','pc_Np1'],['pc_sinner','-','V0kk','pc_kNNp1'],['pc_S','*','pc_kN','pc_sinner']]
 if mode=='scalar':
  extra=[['pc_AUE','*','pc_A','UE'],['pc_twoAUE','*',2,'pc_AUE'],['pc_US','*','U','pc_S'],['pc_center','-','pc_twoAUE','pc_US']]
  degree,scale=202,4
 else:
  extra=[['pc_e2','*','pc_kN','pc_kN'],['pc_U2','*','U','U'],['pc_theta','*','pc_U2','cTR'],['pc_threeE','*',3,'Dtau'],['pc_threeE_e2','+','pc_threeE','pc_e2'],['pc_thetaZc','*','pc_theta','pc_threeE_e2'],['pc_bmc','-','cTR','c'],['pc_Rc','-','pc_thetaZc','pc_bmc'],['pc_E2','*','Dtau','Dtau'],['pc_fourE2','*',4,'pc_E2'],['pc_S2','*','pc_S','pc_S'],['pc_threeS2','*',3,'pc_S2'],['pc_e22','*','pc_e2','pc_e2'],['pc_sum1','+','pc_fourE2','pc_threeS2'],['pc_Sc','+','pc_sum1','pc_e22'],['pc_EV','*','Dtau','V'],['pc_fourEV','*',4,'pc_EV'],['pc_thetaSc','*','pc_theta','pc_Sc'],['pc_Vdiff','-','pc_fourEV','pc_thetaSc'],['pc_Apart','*','pc_A','pc_Vdiff'],['pc_SRc','*','pc_S','pc_Rc'],['pc_twoSRc','*',2,'pc_SRc'],['pc_inner','+','pc_Apart','pc_twoSRc'],['pc_center','*','U','pc_inner']]
  degree,scale=190,16
 for row in g['source']:
  name,op,a,b=row
  if name=='L':
   rows+=common+extra
   if mode=='scalar': rows.append(['L','*','cTR','Bt'])
   else: rows.extend([['pc_b2','*','cTR','cTR'],['L','*','UE','pc_b2']])
   continue
  if name=='LBt' and mode=='scalar': rows.extend([['pc_innerLB','+','L','pc_center'],['LBt','*','V','pc_innerLB']]);continue
  if name=='center' and mode=='whole':rows.extend([['pc_raw_center','-','n','LBt'],['center','-','pc_raw_center','pc_center']]);continue
  if name=='RG':b='pc_scaledG'
  rows.append([name,op,a,b])
  if name=='Dg':rows.append(['pc_scaledG','*',scale,'Dg'])
 g.update(name=f'start4127_positive10_degree{degree}_ops{len(rows)}',source=rows,operations=len(rows),operation_breakdown=dict(sorted(Counter(r[1] for r in rows).items())),exact_degree=degree,mode='free_inverse_'+mode,root_scale=2 if mode=='scalar' else 4,proof='PROOF.md',generation='Free-chart polynomial quotient center, complete signed bootstrap and whole Start4127 interface.',transport_weight='bV' if mode=='scalar' else '(UE)b^2',parent={'path':str(PARENT.relative_to(ROOT)),'sha256':hashlib.sha256(PARENT.read_bytes()).hexdigest()})
 g['normalization']='lambda=q; Y=s; b=cT-R; no positive auxiliary shift; integer polynomial carrier center'
 g['coefficient_binding']['path']='inherited_positive10/native4127/start_only_ports/'
 g['coefficient_binding']['certificate']='inherited_positive10/native4127/start_only_certificate.json'
 return g

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();metrics=[]
 for mode in ['scalar','whole']:
  g=build(mode);p=ROOT/(g['name']+'.json');s=json.dumps(g,indent=2)+'\n'
  if a.check:
   if p.read_text()!=s:raise ValueError('graph mismatch')
  else:p.write_text(s)
  metrics.append({k:g[k] for k in ['name','mode','domain','operations','operation_breakdown','exact_degree','root_scale','transport_weight']})
 p=ROOT/'METRICS.json';s=json.dumps(metrics,indent=2)+'\n'
 if a.check:
  if p.read_text()!=s:raise ValueError('metrics mismatch')
 else:p.write_text(s)
 print(s)
if __name__=='__main__':main()
