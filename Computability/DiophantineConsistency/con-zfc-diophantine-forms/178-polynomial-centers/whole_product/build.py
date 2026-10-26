"""Literal ten-positive degree208 whole-product polynomial center."""
from pathlib import Path
import json,copy,collections,hashlib
ROOT=Path(__file__).resolve().parent
def build(parent):
 e=copy.deepcopy(parent)
 center_rows=[
 ['wp_A','+','Am1',1],
 ['wp_a2','*','kY','kY'],
 ['wp_Yp1','+','Y',1],
 ['wp_kYYp1','*','kY','wp_Yp1'],
 ['wp_sinner','-','V0kk','wp_kYYp1'],
 ['wp_S','*','kY','wp_sinner'],
 ['wp_U2','*','U','U'],
 ['wp_theta','*','wp_U2','cTR'],
 ['wp_threeE','*',3,'Dtau'],
 ['wp_Zc','+','wp_threeE','wp_a2'],
 ['wp_thetaZc','*','wp_theta','wp_Zc'],
 ['wp_bmc','-','cTR','c'],
 ['wp_Rc','-','wp_thetaZc','wp_bmc'],
 ['wp_E2','*','Dtau','Dtau'],
 ['wp_fourE2','*',4,'wp_E2'],
 ['wp_S2','*','wp_S','wp_S'],
 ['wp_threeS2','*',3,'wp_S2'],
 ['wp_a22','*','wp_a2','wp_a2'],
 ['wp_sum1','+','wp_fourE2','wp_threeS2'],
 ['wp_Sc','+','wp_sum1','wp_a22'],
 ['wp_EV','*','Dtau','V'],
 ['wp_fourEV','*',4,'wp_EV'],
 ['wp_thetaSc','*','wp_theta','wp_Sc'],
 ['wp_Vdiff','-','wp_fourEV','wp_thetaSc'],
 ['wp_Apart','*','wp_A','wp_Vdiff'],
 ['wp_SRc','*','wp_S','wp_Rc'],
 ['wp_twoSRc','*',2,'wp_SRc'],
 ['wp_inner','+','wp_Apart','wp_twoSRc'],
 ['wp_W4','*','U','wp_inner']]
 rows=[]
 for row in e['source']:
  row=list(row)
  if row[0]=='L':rows.extend(center_rows)
  if row[0]=='center':
   rows.append(['wp_raw_center',row[1],row[2],row[3]])
   rows.append(['center','-','wp_raw_center','wp_W4']);continue
  if row[0]=='RG':row[3]='wp_G16'
  rows.append(row)
  if row[0]=='Dg':rows.append(['wp_G16','*',16,'Dg'])
 e['source']=rows;e['name']='whole_product116_degree208';e['operations']=len(rows);e['operation_breakdown']=dict(collections.Counter(row[1] for row in rows));e['exact_degree']=208;e['root_scale']=4;e['center_parameter']='whole polynomial product center';e['polynomial_center']=True;e['proof']='PROOF.md';e['parent']={'path':'parent85.json','sha256':hashlib.sha256((ROOT/'parent85.json').read_bytes()).hexdigest()};e['generation']='Integer polynomial-part center of E*V, square transport, norm16G; carrier-level center subtraction.'
 e['center_formula']='S=kY*(ell+k-kY*(Y+1)), e2=(kY)^2, theta=U^2*b, Rc=theta*(3E+e2)-(b-c), Sc=4E^2+3S^2+e2^2, W4=U*(2S*Rc+A*(4E*V-theta*Sc))'
 return e
if __name__=='__main__':
 e=build(json.loads((ROOT/'parent85.json').read_text()));(ROOT/'equation.json').write_text(json.dumps(e,indent=2)+'\n');print(e['name'],e['operations'],e['operation_breakdown'])
