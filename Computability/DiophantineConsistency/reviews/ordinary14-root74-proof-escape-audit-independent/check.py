#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-root74-proof-escape-audit'
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pins={A/'README.md':'89b6a33a5c22ba3168a586acb69102bcf2c59c6b6b08d289a79d3bc7ac3541fc',A/'check_source.py':'9ec38fd4233d217b6d92a882797647ece6a5fd8492a7f886e35e520fed353996',A/'observation.json':'4e6c5e14912242ce3a3942f3143e4e9105415e7200d8f9ae955c5d1438182c6b'}
tail=b"\nIndependent source review: [root74 proof-escape audit](../../reviews/ordinary14-root74-proof-escape-audit-independent/README.md).\n"
for p,h in pins.items():
 if p==A/'README.md':
  data=p.read_bytes();assert hashlib.sha256(data).hexdigest()=='c82bee5b14a030ebc424539d696dddac4b0b4c15afe8ac3432a09c7e2a2c0563'
  assert data.endswith(tail) and hashlib.sha256(data[:-len(tail)]).hexdigest()==h
 else:assert H(p)==h,(str(p),H(p),h)
raw=json.loads((D/'research/ordinary14-root74-endpoint-import-inventory/inventory.json').read_text());slim=json.loads((D/'research/ordinary14-root74-slim-overlay/inventory.json').read_text())
def scrub(s):
 i=0;depth=0;string=False;line=False;out=[]
 while i<len(s):
  if line:
   if s[i]=='\n':line=False;out.append('\n')
   else:out.append(' ')
   i+=1;continue
  if depth:
   if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
   elif s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
   continue
  if string:
   if s[i]=='\\' and i+1<len(s):out.extend('  ');i+=2
   elif s[i]=='"':string=False;out.append(' ');i+=1
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
   continue
  if s.startswith('--',i):line=True;out.extend('  ');i+=2
  elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
  elif s[i]=='"':string=True;out.append(' ');i+=1
  else:out.append(s[i]);i+=1
 assert not depth and not string
 return ''.join(out)
tokens=['sorry','admit','axiom','unsafe','native_decide','run_tac','implemented_by','ofReduceBool','trustCompiler','partial','unsafeCast','sorryAx','panic!','unreachable!'];pattern=re.compile(r"(?<![A-Za-z0-9_'])"+'(?:'+'|'.join(re.escape(x) for x in tokens)+r")(?![A-Za-z0-9_'])")
counts={};classical={}
for label,rows,base in [('bare',raw['drafts_topological'],D),('qualified',raw['qualified_direct_sources'],D),('slim',slim['drafts_topological'],D/'research/ordinary14-root74-slim-overlay')]:
 hits=[];choose=[]
 for r in rows:
  p=base/r['path'];data=p.read_bytes();assert hashlib.sha256(data).hexdigest()==r.get('overlay_sha256',r.get('sha256'))
  text=scrub(data.decode());hits.extend((r['path'],m.group()) for m in pattern.finditer(text));choose.extend((r['path'],m.group()) for m in re.finditer(r'Classical\.(?:choose!_eq_iff_right|choose_spec|choose!|choose|choice)',text))
 assert not hits,(label,hits);counts[label]=len(rows);classical[label]=len(choose)
assert counts=={'bare':159,'qualified':31,'slim':159} and classical['qualified']==4
# Verify every named escape token is observed in code and suppressed in a comment/string.
for t in tokens:
 assert pattern.search(scrub('by '+t+'\n')).group()==t
 assert pattern.search(scrub('/- '+t+' -/ -- '+t+'\n"'+t+'"\n')) is None
r=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90);assert not r.stderr and r.stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'bounded lexical tokens only; no Lean or axiom closure','pins':{str(p.relative_to(D)):h for p,h in pins.items()},'sources':counts,'qualified_classical_selection_hits':classical['qualified'],'synthetic_token_controls':len(tokens),'author_receipt_replayed':True},sort_keys=True,indent=2))
