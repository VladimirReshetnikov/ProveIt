#!/usr/bin/env python3
"""Merge completed snapshots, add cautionary R-includes-1 comparison, write TSV."""
import json,sys,os,csv,math
from diagnostics import LD,theta,PI
root=os.path.dirname(__file__);rows={}
for f in ['initial.json','lambda4_checked.json','lambda5_checked.json','lambda5_a48_checked.json']:
 p=os.path.join(root,f)
 if not os.path.exists(p):continue
 for r in json.load(open(p))['rows']:
  key=(r['lam_target'],r['a'],r['phase_target']);rows[key]=r
out=[]
for key,r in sorted(rows.items()):
 p1=LD(r['p1']);v1=p1*(1-p1);V=LD(r['V']);C=LD(r['C']);Q=LD(r['Q']);mu=LD(r['mu_fraction'])
 Qbad=Q+v1-(2*C*v1+v1*v1)/V
 r['theta_incorrectly_including_part1']=str(theta((mu+p1)%1,Qbad))
 r['discarded_variables_TV_multiplier_bound']=str(np_sqrt:=((2*PI*V)**LD('.5')*LD(r['omitted'])))
 out.append(r)
json.dump({'method':'Numerical Fourier diagnostics, not exact integer counts; see README.md','rigorous':False,'rows':out},open(os.path.join(root,'diagnostics_complete.json'),'w'),indent=2)
fields=['lam_target','a','phase_target','n','K','actual_lambda','mu_minus_target','Q','Q_limit','multiplier','theta_exact_moments','theta_limit','relative_theta_error','theta_incorrectly_including_part1','discarded_variables_TV_multiplier_bound']
with open(os.path.join(root,'diagnostics_table.tsv'),'w') as f:
 w=csv.DictWriter(f,fieldnames=fields,delimiter='\t',extrasaction='ignore');w.writeheader();w.writerows(out)
print('assembled',len(out),'rows')
