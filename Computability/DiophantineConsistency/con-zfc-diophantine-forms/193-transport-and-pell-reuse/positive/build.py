"""Emit two literal positive-domain polynomials from the frozen 87-gate parent."""
from pathlib import Path
import collections,copy,hashlib,json

ROOT=Path(__file__).resolve().parent

def build(parent,kind):
    e=copy.deepcopy(parent)
    shared=[
      ['new_A','+','Am1',1],
      ['new_kZ','*','k','qY'],
      ['new_Zp1','+','qY',1],
      ['new_kZZp1','*','new_kZ','new_Zp1'],
      ['new_Sinner','-','V0kk','new_kZZp1'],
      ['new_S','*','new_kZ','new_Sinner']]
    if kind=='whole190':
        center=shared+[
          ['new_e2','*','new_kZ','new_kZ'],
          ['new_U2','*','U','U'],
          ['new_theta','*','new_U2','cTR'],
          ['new_threeE','*',3,'Dtau'],
          ['new_3Ee2','+','new_threeE','new_e2'],
          ['new_theta3Ee2','*','new_theta','new_3Ee2'],
          ['new_bmc','-','cTR','c'],
          ['new_Rc','-','new_theta3Ee2','new_bmc'],
          ['new_E2','*','Dtau','Dtau'],
          ['new_fourE2','*',4,'new_E2'],
          ['new_S2','*','new_S','new_S'],
          ['new_threeS2','*',3,'new_S2'],
          ['new_e22','*','new_e2','new_e2'],
          ['new_sc1','+','new_fourE2','new_threeS2'],
          ['new_Sc','+','new_sc1','new_e22'],
          ['new_bB','*','cTR','Bt'],
          ['new_ScShift','-','new_Sc','new_bB'],
          ['new_EV','*','Dtau','V'],
          ['new_fourEV','*',4,'new_EV'],
          ['new_thetaSc','*','new_theta','new_ScShift'],
          ['new_Vdiff','-','new_fourEV','new_thetaSc'],
          ['new_Apart','*','new_A','new_Vdiff'],
          ['new_SRc','*','new_S','new_Rc'],
          ['new_twoSRc','*',2,'new_SRc'],
          ['new_omegainner','+','new_Apart','new_twoSRc'],
          ['new_Omega','*','U','new_omegainner']]
        scale,degree=4,190
    elif kind=='quotient202':
        center=shared+[
          ['new_UQE','*','U','new_S'],
          ['new_twoA','*',2,'new_A'],
          ['new_twoAUE','*','new_twoA','UE'],
          ['new_gcenter','-','new_twoAUE','new_UQE']]
        scale,degree=2,202
    else:raise ValueError(kind)
    rows=[]
    for raw in e['source']:
        row=list(raw)
        name=row[0]
        if name=='L':
            rows.extend(center)
            if kind=='whole190':
                continue
            else:
                rows.append(['new_bB','*','cTR','Bt'])
                rows.append(['new_bBcenter','+','new_bB','new_gcenter'])
                continue
        if kind=='quotient202' and name=='LBt':
            row=['LBt','*','V','new_bBcenter']
        if kind=='whole190' and name=='LBt':continue
        if kind=='whole190' and name=='center':
            row=['center','-','n','new_Omega']
        if name=='RG':row[3]='new_scaledG'
        rows.append(row)
        if name=='Dg':rows.append(['new_scaledG','*',scale*scale,'Dg'])
    e.update(name=kind,source=rows,operations=len(rows),
      operation_breakdown=dict(collections.Counter(r[1] for r in rows)),
      exact_degree=degree,root_scale=scale,
      transport_weight='A*U^3*b^2 (folded into Sc)' if kind=='whole190' else 'bV',
      proof='PROOF.md',parent={'path':'parent87.json','sha256':hashlib.sha256((ROOT/'parent87.json').read_bytes()).hexdigest()},
      generation='Polynomial quotient centers composed with free-quotient scaling; folded weighted square transport in principal endpoint.')
    e['coefficient_binding']['path']='coefficients/'
    e['normalization']='lambda=q; Y=s; literal positive auxiliary coordinate T'
    e.pop('mode',None)
    return e

def main():
    parent=json.loads((ROOT/'parent87.json').read_text())
    for kind in ('whole190','quotient202'):
        e=build(parent,kind)
        (ROOT/(kind+'.json')).write_text(json.dumps(e,indent=2)+'\n')
        print(kind,e['operations'],e['operation_breakdown'],e['exact_degree'])

if __name__=='__main__':main()
