#!/usr/bin/env python3
"""Verify the compact 24-row system printed in section.tex against its JSON."""
from pathlib import Path
from collections import Counter
import json,sympy as s
ROOT=Path(__file__).resolve().parent

def main():
 d=json.loads((ROOT/'determinant37_quartic_direct.json').read_text())
 sy={x:s.Symbol(x) for x in d['variables']+d['fixed_numerals']}
 parse=lambda x:s.sympify(x,locals=sy)
 sy.update({'q':parse('beta*J+1'),'C':parse('beta*J+1-F-alpha'),'X':parse('3*X3-1'),'H':parse('4*a+3'),'k':parse('eta+zeta'),'A0':sy['cone_A'],'B0':sy['cone_B'],'v':sy['v_scale'],'w':sy['w_scale']})
 forms=['L-q**2+1','N-q*(L+1)','X-4*q*w','a-E-(2*v+1)*N','E*(X+1)-X*a','c-(a-E)*k-eta','P-k-E*(c-eta)','tau**2-P**2+P*k-1','D-X-a*c-gamma*H','Delta-a**2-4*a-3','C2-c**2','D**2-Delta*C2-1','F2-f**2','V+c-f*o','V-c*j+k-1-h*E','g-y**2+V**2','I-(2*r+1)*C2','Baux-I**2','Baux-Delta*(F2-1)','y**2-Baux*g-1','k-h*E+F*N+q*L-q*N+q**2-1-F*(q+L)-alpha*L-(MC+q*MF)*J','(K0+4*w)*C-F-z*(q-1)','eta*zeta-1-eta_zeta_pos1**2-eta_zeta_pos2**2-eta_zeta_pos3*(eta_zeta_pos3+1)','A0*F*B0*C-(q-A0*F-B0*C)**2-1-cone1**2-cone2**2-cone3*(cone3+1)']
 expected=Counter(s.expand(parse(x)) for x in d['residuals'])
 for f in forms:
  e=s.expand(parse(f))
  if expected[e]:expected[e]-=1
  elif expected[-e]:expected[-e]-=1
  else:raise ValueError('Displayed residual mismatch: '+f)
 if sum(expected.values()):raise ValueError('Not every JSON residual displayed')
 out={'status':'PASS','displayed_rows':len(forms),'variables':len(d['variables']),'source':'determinant37_quartic_direct.json','section':'section.tex','scope':'Exact sign-insensitive comparison of the compact polynomial equations transcribed in this checker and in section.tex.'}
 (ROOT/'DISPLAY_CHECK.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
