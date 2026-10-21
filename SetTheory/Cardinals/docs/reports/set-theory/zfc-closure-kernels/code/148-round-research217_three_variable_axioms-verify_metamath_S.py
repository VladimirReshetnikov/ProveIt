"""Parse retrieved public-domain Metamath table; verify only H/K/Peirce instances and ordinary MP."""
import re,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
s=(ROOT/'metamath_S_source.txt').read_text()
lines={int(i):x for i,x in re.findall(r'^L(\d+): (.*)$',s,re.M)}
text='\n'.join(lines[i] for i in range(16,122))
text=re.sub(r'cite\d+†([^]+)',r'\1',text)
chunks=re.split(r'\n(?=\d+\s+\|)',text)

def parse_infix(s):
 s=re.sub(r'[^()→𝜑𝜓𝜒]','',s)
 def rec(i):
  if s[i]!='(':return {'𝜑':'p','𝜓':'q','𝜒':'r'}[s[i]],i+1
  a,k=rec(i+1);assert s[k]=='→'
  b,j=rec(k+1);assert s[j]==')'
  return (a,b),j+1
 t,k=rec(0);assert k==len(s);return t

def polish(t):return t if isinstance(t,str) else 'C'+polish(t[0])+polish(t[1])
def prefix(s):
 it=iter(s)
 def f():
  c=next(it);return (f(),f()) if c=='C' else c
 t=f();assert list(it)==[];return t

def schema_match(a,b,env=None):
 if env is None:env={}
 if isinstance(a,str):
  if a in env:assert env[a]==b
  else:env[a]=b
 else:
  assert isinstance(b,tuple)
  schema_match(a[0],b[0],env);schema_match(a[1],b[1],env)
 return env

basis={'ax-1':prefix('CpCqp'),'imim1':prefix('CCpqCCqrCpr'),'peirce':prefix('CCCpqpp')}
proof={};rows=[];counts={x:0 for x in basis};counts['ax-mp']=0
for chunk in chunks:
 fields=chunk.split('|');assert len(fields)==4,(len(fields),chunk[:80])
 n=int(fields[0].strip());hyps=list(map(int,re.findall(r'\d+',fields[1])));name=fields[2].split()[0]
 t=parse_infix(fields[3]);row={'id':n,'polish':polish(t),'rule':name}
 if name=='ax-mp':
  assert len(hyps)==2
  minor,major=(proof[i] for i in hyps)
  assert isinstance(major,tuple) and major==(minor,t)
  row['parents_minor_major']=hyps
 else:
  assert name in basis and not hyps
  row['substitution']={k:polish(v) for k,v in schema_match(basis[name],t).items()}
 counts[name]+=1;proof[n]=t;rows.append(row)
assert len(rows)==97 and list(proof)==list(range(1,98))
assert polish(proof[97])=='CCpCqrCCpqCpr'
(ROOT/'H_K_P_to_S_certificate.json').write_text(json.dumps({'source':'https://us.metamath.org/mpeuni/tarski-bernays-ax2.html','status':'PASS','counts':counts,'rows':rows},indent=2)+'\n')
print('PASS: independently verified all97 Metamath rows, only H/K/Peirce schema instances + ordinary MP.',counts)
