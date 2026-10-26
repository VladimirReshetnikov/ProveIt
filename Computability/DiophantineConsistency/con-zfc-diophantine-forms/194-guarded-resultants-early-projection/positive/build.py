#!/usr/bin/env python3
"""Free-chart compositions of quotient and whole-product polynomial centers.
Source178 is credited for the A-quotient and full-product center; our t=A-1
quotient and first-product truncation are derived in PROOF.md.
"""
from pathlib import Path
from collections import Counter
import argparse,copy,hashlib,json
ROOT=Path(__file__).resolve().parent
SPECS={'quotient_t':(97,202,2),'product2':(111,198,2),'product4':(119,190,4)}
def center(mode):
    rows=[['cy','*','q','kY']]
    if mode=='quotient_t':
        rows += [['cyy','*','cy','qY'],['qt_inner','-','V0kk','cyy'],['Qt','*','cy','qt_inner'],['twoA','+','Am1','Ap1'],['twice_upper','*','twoA','UE'],['UQt','*','U','Qt'],['center_root','-','twice_upper','UQt']]
        return rows
    rows += [['Yp1','+','qY',1],['cyYp1','*','cy','Yp1'],['sinner','-','V0kk','cyYp1'],['S','*','cy','sinner'],['U2','*','U','U'],['theta','*','U2','cTR']]
    if mode=='product2':
        rows += [['thetaE','*','theta','Dtau'],['fourthetaE','*',4,'thetaE'],['bmc','-','cTR','c'],['Rc','-','fourthetaE','bmc'],['E2','*','Dtau','Dtau'],['S2','*','S','S'],['Sc','+','E2','S2'],['EV','*','Dtau','V'],['thetaSc','*','theta','Sc'],['Vdiff','-','EV','thetaSc'],['twoA','+','Am1','Ap1'],['Apart','*','twoA','Vdiff'],['SRc','*','S','Rc'],['whole_inner','+','Apart','SRc'],['Omega','*','U','whole_inner']]
    else:
        rows += [['A','+','Am1',1],['e2','*','cy','cy'],['threeE','*',3,'Dtau'],['Zc','+','threeE','e2'],['thetaZc','*','theta','Zc'],['bmc','-','cTR','c'],['Rc','-','thetaZc','bmc'],['E2','*','Dtau','Dtau'],['fourE2','*',4,'E2'],['S2','*','S','S'],['threeS2','*',3,'S2'],['e22','*','e2','e2'],['sum1','+','fourE2','threeS2'],['Sc','+','sum1','e22'],['EV','*','Dtau','V'],['fourEV','*',4,'EV'],['thetaSc','*','theta','Sc'],['Vdiff','-','fourEV','thetaSc'],['Apart','*','A','Vdiff'],['SRc','*','S','Rc'],['twoSRc','*',2,'SRc'],['whole_inner','+','Apart','twoSRc'],['Omega','*','U','whole_inner']]
    return rows

def construct(mode,tuple_name='radix67'):
    p=ROOT/'parent/positive10_degree214_ops87.json';g=json.loads(p.read_text());rows=[]
    for name,op,a,b in g['source']:
        if name=='L':
            rows += center(mode)
            if mode=='quotient_t':
                rows += [['bB','*','cTR','Bt'],['bB_center','+','bB','center_root']]
                continue
        if mode=='product4' and name=='L':a,b='cTR','cTR'
        if mode=='quotient_t' and name=='LBt':a,b='V','bB_center'
        if name=='center' and mode!='quotient_t':
            rows += [['raw_center',op,a,b],['center','-','raw_center','Omega']];continue
        if name=='RG':b='scaledG'
        rows.append([name,op,a,b])
        if name=='Dg':rows.append(['scaledG','*',SPECS[mode][2]**2,'Dg'])
    if tuple_name=='radix67':
        g['coefficient_binding']['path']='parent/'+g['coefficient_binding']['path'];g['coefficient_binding']['endianness']='little'
    else:
        native=json.loads((ROOT/'native2963/candidates/one-page-low-padding2963/polynomial.json').read_text());g['coefficient_binding']=copy.deepcopy(native['coefficient_binding']);g['coefficient_binding'].update(path='native2963/candidates/one-page-low-padding2963/coefficients',endianness='big',ordinary_proof='native2963/research/low-padding-independent/PROOF.md',certificate='native2963/research/low-padding-independent/certificate.json')
    n,d,r=SPECS[mode]
    if len(rows)!=n:raise ValueError((mode,len(rows),n))
    g.update(transport_weight='b2' if mode=='product4' else 'bV',name=mode+'_'+tuple_name,mode=mode,tuple_name=tuple_name,source=rows,operations=len(rows),exact_degree=d,root_scale=r,operation_breakdown=dict(sorted(Counter(row[1] for row in rows).items())),parent={'path':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()},proof='PROOF.md',generation='Free chart Y=s, lambda=q, inverse-Lucas correction; early p=3 projector exclusion; bV or b2 transport; exact polynomial center and square-scaled norm.',status='Ordinary proof at separately retained coherent native/refutation calibration; no formal-kernel replay.')
    return g

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
    tuples=['radix67','low2963']
    for mode in SPECS:
        for t in tuples:
            g=construct(mode,t);p=ROOT/(g['name']+'.json');s=json.dumps(g,indent=2)+'\n'
            if a.check:
                if p.read_text()!=s:raise ValueError('rebuild '+p.name)
            else:p.write_text(s)
            print(p.name,g['operations'],g['exact_degree'])
if __name__=='__main__':main()
