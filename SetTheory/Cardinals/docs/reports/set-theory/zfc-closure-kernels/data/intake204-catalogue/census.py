from pathlib import Path
import subprocess,re,json,collections
base=Path('SetTheory/Cardinals/docs/reports');s=(base/'manifest.tex').read_text();entries=[]
def arg(i):
 assert s[i]=='{';depth=1;j=i+1
 while depth:
  if s[j]=='\\':j+=2;continue
  if s[j]=='{':depth+=1
  if s[j]=='}':depth-=1
  j+=1
 return s[i+1:j-1],j
for m in re.finditer(r'^\\entry\{',s,re.M):
 i=m.end()-1;a=[]
 for _ in range(5):
  while s[i].isspace():i+=1
  t,i=arg(i);a.append(t)
 entries.append({'title':a[0],'directory':a[1],'main':a[2]})
assert len(entries)==290 and len({r['directory'] for r in entries})==290
files=subprocess.check_output(['git','ls-files',str(base)],text=True).splitlines();dirs={str(Path(p).parent) for p in files}
for r in entries:
 p=str(base/r['directory']);assert any(d==p or d.startswith(p+'/') for d in dirs),p
roots=[str(base/r['directory']) for r in entries]
uncovered=[p for p in files if p.endswith(('.tex','.pdf')) and p not in [str(base/'manifest.tex'),str(base/'manifest.pdf')] and not any(p.startswith(r+'/') for r in roots)]
res={'status':'CATALOGUE_DIRECTORY_CENSUS_PASS','entry_count':len(entries),'report_count':290,'category_counts':dict(collections.Counter(r['directory'].split('/')[0] for r in entries)),'uncovered_tex_pdf':uncovered,'directories':[r['directory'] for r in entries]}
Path('/tmp/zfc-intake204-catalogue/census.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps({k:v for k,v in res.items() if k!='directories'},indent=2))
