#!/usr/bin/env python3
"""Check explanatory gate aliases against both graph and displayed TeX/PDF."""
from pathlib import Path
import hashlib,json,re,subprocess
D=Path(__file__).resolve().parent; R=D.parents[1]; H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=[Path(__file__).resolve()]; results={}
for n in (29,30):
 tex=R/f'equation8-{n}.tex';pdf=R/f'equation8-{n}.pdf';graph=R/f'research/adaptive-square-sums{n}-degree8/candidate.json';files += [tex,pdf,graph]
 t=tex.read_text(); c=json.loads(graph.read_text());rows={r[0]:r for r in c['source']};w=c['witnesses']
 expected={'q3':['q3','*','q','qSquareVariable'],'g55':['g55','*','productVariable2','q'],'g39':['g39','*','scaleVariable','scaleVariable'],'y2':['y2','*','y','y'],'g80':['g80','*','vValueVariable','vValueVariable'],'E':['E','*','X','Y'],'I':['I','*','cSquareVariable','i'],'a':['a','+','productVariable2','Y'],'g25':['g25','*','K0','q'],'g26':['g26','+','X','g25'],'g27':['g27','*','C','g26'],'g28':['g28','*','F','q'],'Bt':['Bt','-','g27','g28'],'f2':['f2','*','f','f']}
 for key,val in expected.items():assert rows[key]==val,(n,key)
 for name in ['cVariable','ellVariable','cSquareVariable','zValueVariable','dValueVariable','vValueVariable','deltaVariable','qSquareVariable','productVariable2','scaledIndexVariable','qValueVariable']:assert name in w
 assert ('fSquareVariable' in w)==(n==30)
 for s in [r'\texttt{cNamed, ellNamed} are $c,\ell$',r'gate \texttt{a} is the displayed abbreviation',r'gate \texttt{WComputed} is the displayed abbreviation $W=C(X+Kq)-Fq$',r'Gates \texttt{q3, g55, g39, y2, g80} compute $s,x,\sigma,\nu,\vartheta$',r'Gates \texttt{E, I} compute',r'$XY,ng$; the display uses $E=\lambda$, $I=\theta$',r'a=\lambda+Y,\quad s=q\kappa,\quad x=\lambda q',r'\sigma=\psi^2,\quad\nu=\upsilon^2',r'\vartheta=V^2',r'E=\lambda',r'I=\theta']:
  assert s in t,(n,s)
 for line in ['4. q3 = q * kappa','8. E = X * Y','13. a = lambda + Y','22. g25 = K * q','23. g26 = X + g25','24. g27 = C * g26','25. g28 = F * q','26. WComputed = g27 - g28','37. g39 = psi * psi','53. g55 = lambda * q','68. I = n * g','75. y2 = upsilon * upsilon','76. g80 = V * V']:
  assert line+r'\\' in t,(n,line)
 if n==29:
  assert r'gate \texttt{m} is $m=f^2$' in t and r'gate \texttt{f2} is $m=f^2$' not in t
  assert r'm=f^2' in t and '65. m = f * f'+r'\\' in t
 else:
  assert r'\texttt{m, n, Z, D, V, delta} are the displayed' in t
  assert r'\mathcal{Z}=m-f^2' in t and '65. f2 = f * f'+r'\\' in t
  assert rows['fSquareDifference']==['fSquareDifference','-','fSquareVariable','f2']
 text=subprocess.run(['pdftotext','-layout','-f','2','-l','2',str(pdf),'-'],check=True,capture_output=True,text=True).stdout
 assert 'gate WComputed is the displayed' in text and 'Gates E, I compute XY, ng' in text
 if n==29:assert 'and gate m is m = f' in text and 'and gate f2 is' not in text
 results[str(n)]={'pdf_sha256':H(pdf),'tex_sha256':H(tex),'candidate_sha256':H(graph),'printed_square_gate':'m' if n==29 else 'f2','square_coordinate':'abbreviation' if n==29 else 'positive input'}
out={'status':'PASS_EXPLANATORY_ALIASES','files_sha256':{str(p):H(p) for p in files},'results':results,'scope':'Checks explanatory alias claims against candidate gate rows, printed circuit, TeX definitions and extracted PDF text; E=λ and I=θ are zero-set constraints, not identities at arbitrary assignments. Does not replay Lean.'}
p=D/'receipt.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],H(p))
