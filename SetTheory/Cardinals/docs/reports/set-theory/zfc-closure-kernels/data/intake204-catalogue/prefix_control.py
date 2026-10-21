from pathlib import Path
import hashlib,json,re,subprocess
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');O=Path('/tmp/zfc-intake204-catalogue')
p='SetTheory/Cardinals/docs/reports/manifest.tex'
old=subprocess.check_output(['git','show','HEAD:'+p],cwd=R,text=True)
new=(R/p).read_text()
def sha(s): return hashlib.sha256(s.encode()).hexdigest()
def entry(s):
 i=s.index(r'\entry{ZFC closure kernels and small inconsistency-search machines}')+len(r'\entry')
 args=[]
 for _ in range(5):
  while s[i].isspace():i+=1
  assert s[i]=='{';begin=i+1;depth=1;i+=1
  while depth:
   if s[i]=='\\':i+=2;continue
   if s[i]=='{':depth+=1
   if s[i]=='}':depth-=1
   i+=1
  args.append(s[begin:i-1])
 return args
x,y=entry(old),entry(new)
assert x[:3]==y[:3]
assert y[3].startswith(x[3]),'Original archive list changed'
append=y[3][len(x[3]):]
expected=r'; batch~200 (placed, written follow-up pending): zfc214-investigation-2026-10-21.zip (\texttt{3249800496}) and Transfer\_Compiler\_201\_Nodes\_214\_Target\_Unmet\_2026-10-21.zip (\texttt{7342ae8c96}); batch~204: Proof\_Simplification\_and\_GC-ZC215\_2026-10-21.zip (\texttt{05d063acef})'
assert append==expected
for b in range(195,200):assert f'batch~{b}:' in x[3]
def placements(s):
 a=s.index(r'{\raggedright\footnotesize Placements ',s.index(r'\entry{ZFC closure kernels'))
 b=s.index(';\narticles recoverable',a)
 return s[a:b]
px,py=placements(old),placements(new)
assert py==px+r', \texttt{fc750e0e30}, \texttt{ec445a5246}'
record={'status':'EXACT_PREFIX_PRESERVATION_PASS','basis_head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'old_manifest_sha256':sha(old),'new_manifest_sha256':sha(new),'archive_list':{'old_characters':len(x[3]),'old_sha256':sha(x[3]),'old_prefix_preserved_exactly':True,'already_present_batches':[195,196,197,198,199],'appended_batches':[200,204],'exact_append':append},'placement_list':{'old_prefix_preserved_exactly':True,'old_sha256':sha(px),'exact_append':py[len(px):]},'unchanged_entry_fields':['title','directory','main_document']}
(O/'prefix-control.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
