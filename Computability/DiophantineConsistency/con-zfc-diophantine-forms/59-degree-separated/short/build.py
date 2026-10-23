#!/usr/bin/env python3
"""New literal generators. No imported upstream generator or checker is executed."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
CASES=[
 ('p67_d125',True,False,False,'scaled_product',None,15),
 ('p68_d101',True,False,False,'product',None,15),
 ('p69_d91',True,True,False,'product',None,15),
 ('p70_d84',True,True,True,'product',None,15),
 ('p71_d80',True,False,False,'sos',[['N0','N1'],['Na','Nk','Nt']],15),
 ('p72_d74',True,True,False,'sos',[['N0','N1','Nk'],['Na','Nt']],15),
 ('p73_d60',True,False,False,'sos',[['N0'],['Na'],['N1','Nk','Nt']],15),
 ('p74_d50',True,False,True,'sos',[['Na'],['N1','Nk'],['N0','Nt']],15),
 ('p75_d46',True,True,True,'sos',[['Na'],['N0','Nk'],['N1','Nt']],15),
 ('p76_d44_reference',False,True,True,'sos',[['Na'],['N0','Nk'],['N1','Nt']],15),
 ('p79_d52_14positive',True,False,True,'sos',None,14),
]
def build(case):
 name,squared,g0,ga,kind,groups,nv=case
 rows=[]
 def g(n,o,a,b):rows.append([n,o,a,b]);return n
 g('q1','*','beta','J');g('q','+','q1',1);g('q2','*','q','q');g('q3','*','q2','q')
 g('X','*','w','q');g('Y','*','s','q3');g('E','*','X','Y');g('k','+','eta','zeta')
 g('kY','*','k','Y');g('L','*','E','kY')
 if g0:
  g('r2','*','r','r');g('twice_r','*',2,'r');g('first_gap','-','twice_r','k');g('first_term','*','L','first_gap');g('N0','+','r2','first_term')
 else:
  g('Lplusk','+','L','k');g('first_term','*','L','Lplusk');g('tau2','*','tau','tau');g('N0','-','tau2','first_term')
 g('c','+','kY','eta');g('a','+','E','Y');g('ac','*','a','c');g('b0','+','X','ac');g('foura','*',4,'a');g('H','+','foura',3)
 g('a2','*','a','a');g('Delta','+','a2','H');g('c2','*','c','c');g('Dc2','*','Delta','c2')
 g('qF','-','q','F');g('C','-','qF','alpha');g('Gpart','*','q1','qF');g('G','+','Gpart','alpha');g('q2m1','-','q2',1)
 g('Rpart','*','G','q2m1');g('qMF','*','q','MF');g('Mpart','+','MC','qMF');g('mask','*','Mpart','J');g('R','+','Rpart','mask')
 if nv==15:
  g('gammaH','*','gamma','H');g('D','+','b0','gammaH');g('D2','*','D','D');g('N1','-','D2','Dc2')
  g('hE','*','h','E');g('k_hE','-','k','hE');g('Nk','-','k_hE','R')
 else:
  g('q4','*','q2','q2');g('U','*',4,'q4');g('main_target','+','Dc2',1);g('k_R','-','k','R');g('index_gap','-','k_R',1)
  g('Ugamma','*','U','gamma');g('carrier','-','Ugamma','index_gap');g('Hcarrier','*','H','carrier');g('Ub0','*','U','b0')
  g('Dstar','+','Ub0','Hcarrier');g('Dstar2','*','Dstar','Dstar');g('U2','*','U','U');g('U2target','*','U2','main_target');g('main_residual','-','Dstar2','U2target')
 g('Kw','+','K0','w');g('KwC','*','Kw','C');g('transport_partial','+','KwC','qF');g('zq1','*','z','q1');g('Nt','-','transport_partial','zq1')
 g('f2','*','f','f')
 if squared:
  g('cT','*','c','T');g('cT_R','-','cT','R');g('f2inner','*','f2','cT_R');g('V','-','f2inner','c')
 else:
  g('Tf','*','T','f');g('Tfm1','-','Tf',1);g('cTfm1','*','c','Tfm1');g('Rf2','*','R','f2');g('V','-','cTfm1','Rf2')
 g('I','*','i','Dc2' if kind=='scaled_product' else 'c2');g('I2','*','I','I')
 if kind=='scaled_product':
  g('scaled_f2','*','Delta','f2');g('Aaux','-','scaled_f2','Delta')
 else:
  g('f2m1','-','f2',1);g('Aaux','*','Delta','f2m1')
 if ga:
  g('yhat','+','V','u');g('yhat2','*','yhat','yhat');g('V_yhat','+','V','yhat');g('gap_product','*','u','V_yhat');g('aux_term','*','Aaux','gap_product');g('Na','-','yhat2','aux_term')
 else:
  g('V2','*','V','V');g('y2','*','y','y');g('aux_gap','-','V2','y2');g('aux_term','*','Aaux','aux_gap');g('Na','+','aux_term','y2')
 def product(xs,prefix):
  out=xs[0]
  for j,x in enumerate(xs[1:]):out=g(prefix+str(j),'*',out,x)
  return out
 if kind=='scaled_product':
  g('Nstrong','-','scaled_f2','I2');prod=product(['N0','N1','Na','Nk','Nt','Nstrong'],'prod');g('polynomial','-',prod,'Delta')
 elif kind=='product':
  g('strong_residual','-','I2','Aaux');g('Ns','+','strong_residual',1)
  prod=product(['N0','N1','Na','Nk','Nt','Ns'],'prod');g('polynomial','-',prod,1)
 else:
  residuals=[]
  if nv==14:
   residuals=['main_residual'];groups=[['Na'],['N0','Nt']]
  for j,block in enumerate(groups):
   prod=product(block,'group'+str(j)+'_');residuals.append(g('res'+str(j),'-',prod,1))
  residuals.append(g('strong_residual','-','I2','Aaux'))
  squares=[g('sq'+str(j),'*',r,r) for j,r in enumerate(residuals)]
  out=squares[0]
  for j,x in enumerate(squares[1:]):out=g('polynomial' if j==len(squares)-2 else 'sum'+str(j),'+',out,x)
 witnesses=['J','F','alpha','z','f']+(['h'] if nv==15 else[])+['i','T','s','w','r' if g0 else'tau','eta','zeta','u' if ga else'y','gamma']
 return dict(name=name,witness_domain='strictly positive integers',witnesses=witnesses,fixed_numerals=['beta','K0','MC','MF'],source=rows,output='polynomial',options=dict(squared_modulus=squared,first_gap=g0,aux_gap=ga,kind=kind,groups=groups,variables=nv),coefficient_binding='../COEFFICIENT_BINDING.json',proof_boundary='Ordinary mathematical reduction through included compiler/Pell interfaces; not a newly kernel-checked theorem.')
if __name__=='__main__':
 out=ROOT/'circuits';out.mkdir(exist_ok=True)
 for case in CASES:
  data=build(case);(out/(data['name']+'.json')).write_text(json.dumps(data,indent=2)+'\n');print(data['name'],len(data['source']))
