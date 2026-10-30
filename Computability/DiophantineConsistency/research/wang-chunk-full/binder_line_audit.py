"""Exploratory text-only audit of reprStr binder names; not kernel alpha checking."""
from pathlib import Path
import re,sys,json
if len(sys.argv)!=3: raise SystemExit('usage: binder_line_audit.py historical.log replacement.log')
def parse(p):
 s=Path(p).read_text();m=list(re.finditer(r'^EXPORT (.*?) :::',s,re.M));assert m and s.startswith('EXPORT ');d={}
 for i,x in enumerate(m):
  n=x.group(1);assert n not in d;d[n]=s[x.end():m[i+1].start() if i+1<len(m) else len(s)].strip()
 return d
def norm(s):return re.sub(r'(Lean\.Expr\.(?:forallE|lam)\n)[^\n]*\n',r'\1  <binder>\n',s)
a=parse(sys.argv[1]);b=parse(sys.argv[2]);raw=sorted(n for n in a.keys()&b.keys() if a[n]!=b[n]);after=sorted(n for n in raw if norm(a[n])!=norm(b[n]));print(json.dumps({'historical_count':len(a),'replacement_count':len(b),'missing':sorted(a.keys()-b.keys()),'raw_mismatch':raw,'binder_line_normalized_mismatch':after,'scope':'text-only normalization of the line after forallE/lam; not a kernel alpha-equivalence check'},indent=2))
