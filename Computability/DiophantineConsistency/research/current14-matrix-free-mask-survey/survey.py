#!/usr/bin/env python3
"""Read-only base source paths and theorem anchors for the matrix-free client."""
import collections,hashlib,json,re
from pathlib import Path
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3]
MANIFEST=Path('/tmp/current14-standard-fresh-source-20261104/manifest.json');OUT=HERE/'observation.json'
EXPECT='1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
need(not OUT.exists() and sha(MANIFEST)==EXPECT,'existing output or wrong base manifest')
m=json.loads(MANIFEST.read_text());rows=m['sources'];start='DiophantineConsistency.IPRAStandardCurrentEndpoint'
anchors={'DiophantineConsistency.ArithmeticMaskData':['lowList_identity','lowPort_ofDigits','sum_range_pow','sum_Ico_pow','support_value','ofDigits_replicate_append','G_succ','highPort_ofDigits'],
         'DiophantineConsistency.MFCurrentKernel2011':['geometric','phi','phi_printed','K_printed'],
         'DiophantineConsistency.MFPaper1982Digits':['ofDigits_replicate'],
         'DiophantineConsistency.CurrentMaskData2011':['beta','lowPort','highPort','ports']}
def find(target):
 q=collections.deque([start]);parents={start:None}
 while q:
  n=q.popleft()
  if n==target:
   path=[]
   while n is not None:path.append(n);n=parents[n]
   return path[::-1]
  if n not in rows:continue
  for d in rows[n]['imports']:
   if d not in parents:parents[d]=n;q.append(d)
 return None
results={}
for name,names in anchors.items():
 need(name in rows,('missing base module',name));path=find(name);need(path is not None,('module not endpoint ancestor',name))
 r=rows[name];source=ROOT/r['workspace_path'];need(source.is_file() and sha(source)==r['sha256'],('source drift',name));text=source.read_text();lines={}
 for item in names:
  matches=[i for i,line in enumerate(text.splitlines(),1) if re.match(r'^\s*(?:(?:private|protected|noncomputable|irreducible_def)\s+)*(?:theorem|lemma|def|abbrev)\s+'+re.escape(item)+r"(?![A-Za-z0-9_'])",line)]
  if not matches and item in ('lowPort',):matches=[i for i,line in enumerate(text.splitlines(),1) if re.match(r'^\s*def\s+'+re.escape(item)+r"(?![A-Za-z0-9_'])",line)]
  need(len(matches)==1,('theorem anchor mismatch',name,item,matches));lines[item]=matches[0]
 results[name]={'path_from_endpoint':path,'workspace_path':r['workspace_path'],'sha256':r['sha256'],'anchors':lines}
result={'status':'SOURCE_SURVEY_ONLY','snapshot_sha256':EXPECT,'script_sha256':sha(__file__),'modules':results,
        'scope':'Pinned source-declared import paths and textual theorem anchors; no new client elaboration or proof.'}
with OUT.open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps({'status':result['status'],'modules':len(results)},sort_keys=True))
