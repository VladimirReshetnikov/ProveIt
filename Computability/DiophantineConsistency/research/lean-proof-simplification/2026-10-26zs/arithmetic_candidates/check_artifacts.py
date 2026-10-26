"""Static/patch/arithmetic checks, not Lean elaboration or kernel validation."""
from pathlib import Path
import json,re,subprocess,tempfile,hashlib

def require(condition, message="Required check failed"):
    if not condition:
        raise RuntimeError(message)

root=Path(__file__).resolve().parent
a=root
p=Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPackingRank2011.lean')
s=(root/'source/CurrentPackingRank2011.lean').read_text()
results=[]
for directory,patch in [('fourblocks_certificate','fourblocks_certificate.patch'),('rank_growth','rank_growth.patch'),('combined','combined.patch')]:
 c=(a/directory/'candidate/CurrentPackingRank2011.lean').read_text()
 with tempfile.TemporaryDirectory(prefix='round6-patch-',dir='/tmp') as temp:
  target=Path(temp)/p;target.parent.mkdir(parents=True);target.write_text(s)
  cp=subprocess.run(['patch','--batch','--fuzz=0','-p1','-i',str(a/directory/patch)],cwd=temp,capture_output=True,text=True)
  require(cp.returncode == 0, cp.stdout + cp.stderr)
  require(target.read_text() == c)
 # Declaration headers/statements prior to ':= by', and all definitions, identical.
 def headers(t):
  lines=t.splitlines();out=[];i=0
  while i<len(lines):
   if re.match(r'^(theorem|def)\s',lines[i]):
    block=lines[i];i+=1
    while ':=' not in block:
     block+='\n'+lines[i];i+=1
    out.append(block.split(':=',1)[0])
   else:i+=1
  return out
 require(headers(s) == headers(c))
 def erase_target_bodies(t):
  if directory in ('fourblocks_certificate','combined'):
   t=re.sub(r'(?ms)(^theorem fourBlocks_cast .*?:= by\n).*?(?=\nomit \[NeZero N\] in)',r'\1<proof body>\n',t)
  if directory in ('rank_growth','combined'):
   t=re.sub(r'(?ms)(^theorem rank_gt_twice_window .*?:= by\n).*?(?=\ntheorem fourBlocks_population)',r'\1<proof body>\n',t)
  return t
 require(erase_target_bodies(s) == erase_target_bodies(c), 'Change outside target proof bodies')
 require(re.findall('^import .*$', s, re.M) == re.findall('^import .*$', c, re.M))
 require(not re.search('\\b(sorry|admit|axiom)\\b', c))
 results.append({'candidate':directory,'patch_replay':'PASS exact fuzz=0','statement_headers':'PASS unchanged','outside_target_proof_bodies':'PASS byte-identical','imports':'PASS unchanged','new_proof_holes':'none','sha256':hashlib.sha256(c.encode()).hexdigest()})
# Numeric growth spot checks include u=0, which old auxiliary positivity chain excluded.
for u in range(4097):
 require((2 ** u) ** 3 == 2 ** (u * 3))
 require(2 * u <= 3 * u < 2 ** (u * 3))
out={'status':'PASS non-Lean checks only; all candidates UNCOMPILED','checks':results,'growth_samples':4097,'growth_includes_zero':True,'growth_scope':'Comparison-only prior mechanism, no new simplification credit','lean_execution':'NOT RUN; no installation authorized'}
(a/'artifact_checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
