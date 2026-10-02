"""Fail on symbolic or exact-count disagreement; compare replay diagnostics."""
import json, math, sys
from pathlib import Path
import sympy as s
r=Path(__file__).resolve().parent.parent
c=r/'checks'
def read(name):return json.loads((c/name).read_text())
x=s.symbols('x')
expected={
'1':(x*x+8)/6,
'2':x*(x**4+11*x*x-6)/72,
'3':(5*x**8+40*x**6-561*x**4-1074*x*x-4848)/6480,
'4':x*(5*x**10-5*x**8-1539*x**6+3339*x**4+15264*x*x+173988)/155520}
a=read('central-polynomials.json'); b=read('independent-central-results.json')
for j,p in expected.items():
 assert s.expand(s.sympify(a[j])-p)==0,('central',j)
 assert s.expand(s.sympify(b['central'][j])-p)==0,('independent central',j)
diag={'1':'4/3','2':'0','3':'-101/135','4':'0','5':'19819/7560','6':'0','7':'-4463177/272160'}
d=read('diagonal-coefficients.json')
for j,v in diag.items():
 assert s.sympify(d[j])==s.sympify(v),('diagonal',j)
 assert s.sympify(b['diagonal'][j])==s.sympify(v),('independent diagonal',j)
counts={1:1,2:5,3:1306,4:46922017,5:449363984934526}
for row in read('renewal-exact-checks.json'):
 if row['m'] in counts: assert int(row['a'])==counts[row['m']]
for n,a in counts.items():assert b['word_counts'][str(n)]==a
rr=read('independent-rare-results.json')
for row in read('rare-tail-exact-checks.json'):
 alt=next(z for z in rr['exact_checks'] if (z['m'],z['k'])==(row['m'],row['k']))
 assert math.isclose(row['tail'],float(alt['tail']),rel_tol=1e-13)
 assert math.isclose(row['ratio'],float(alt['exact_over_leading']),rel_tol=1e-12)
 assert math.isclose(row['first_ratio'],float(alt['exact_over_first']),rel_tol=1e-12)
# When baseline files are provided, compare structure with tight numeric tolerance.
if len(sys.argv)>1:
 base=Path(sys.argv[1])
 def equal(a,b,p='root'):
  if isinstance(a,dict):
   assert isinstance(b,dict) and set(a)==set(b),p
   for k in a:equal(a[k],b[k],p+'.'+k)
  elif isinstance(a,list):
   assert isinstance(b,list) and len(a)==len(b),p
   for i,(aa,bb) in enumerate(zip(a,b)):equal(aa,bb,p+f'[{i}]')
  elif isinstance(a,(int,float)) and not isinstance(a,bool):
   assert a==b or math.isclose(a,b,rel_tol=1e-12,abs_tol=1e-14),(p,a,b)
  else:assert a==b,(p,a,b)
 for f in sorted(c.glob('*.json')):equal(json.loads(f.read_text()),json.loads((base/f.name).read_text()),f.name)
print('PASS: four central polynomials, seven diagonal orders, exact counts, rare-tail agreement, and replay comparison')
