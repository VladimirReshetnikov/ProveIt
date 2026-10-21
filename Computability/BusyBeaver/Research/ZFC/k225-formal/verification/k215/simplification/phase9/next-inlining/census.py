"""Conservative source-level caller census; not elaborated Lean dependency analysis."""
from pathlib import Path
import hashlib,json,re,collections,bisect
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs');OUT=Path(__file__).resolve().parent
B=ROOT/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
modules=[x['module'].split('.')[-1] for x in json.load(open('/tmp/k215-phase9-main/full-v1.json'))['modules']]+['DomRho8','KSeed222','KSeedModel222','DominatedImplication']
def pin(p):
 b=p.read_bytes();return dict(path=str(p.relative_to(ROOT)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),lines=len(b.splitlines()))
def strip(s):
 out=list(s);i=0;depth=0;quoted=False
 while i<len(s):
  if depth:
   if s[i:i+2]=='/-':out[i:i+2]='  ';depth+=1;i+=2
   elif s[i:i+2]=='-/':out[i:i+2]='  ';depth-=1;i+=2
   else:
    if s[i]!='\n':out[i]=' '
    i+=1
  elif quoted:
   if s[i]=='\\':out[i]=' ';i+=1;out[i]=' ';i+=1
   else:
    if s[i]=='"':quoted=False
    if s[i]!='\n':out[i]=' '
    i+=1
  elif s[i:i+2]=='/-':out[i:i+2]='  ';depth=1;i+=2
  elif s[i:i+2]=='--':
   j=s.find('\n',i);j=len(s)if j<0 else j;out[i:j]=' '*(j-i);i=j
  elif s[i]=='"':out[i]=' ';quoted=True;i+=1
  else:i+=1
 assert not depth and not quoted
 return ''.join(out)
pat=re.compile(r'^(?P<private>private\s+)?(?P<kind>theorem|lemma|def|abbrev|structure|inductive)\s+(?P<name>[\w.]+)\b',re.M)
parsed={}
for p in sorted((ROOT/'Computability/BusyBeaver/Lean').rglob('*.lean')):
 s=strip(p.read_text());ms=list(pat.finditer(s));ds=[]
 for i,m in enumerate(ms):
  stop=ms[i+1].start()if i+1<len(ms)else len(s)
  chunk=s[m.start():stop];end=re.search(r'^(?:end|namespace|section|#print|attribute|open|variable|include|omit|set_option)\b',chunk,re.M)
  if end:chunk=chunk[:end.start()];stop=m.start()+len(chunk)
  ds.append(dict(name=m['name'],kind=m['kind'],private=bool(m['private']),start=m.start(),end=stop,line=s.count('\n',0,m.start())+1,lines=len(chunk.rstrip().splitlines()),bytes=len(chunk.rstrip().encode()),text=chunk))
 parsed[str(p)]=(s,ds)
names={d['name'].split('.')[-1] for mod in modules for d in parsed[str(B/(mod+'.lean'))][1]}
index=collections.defaultdict(list)
for path,(t,ts) in parsed.items():
 starts=[d['start']for d in ts]
 line_starts=[0]+[m.end()for m in re.finditer('\n',t)]
 for hit in re.finditer(r"[A-Za-z_][A-Za-z_0-9']*",t):
  base=hit[0]
  if base not in names:continue
  idx=bisect.bisect_right(starts,hit.start())-1
  owner=ts[idx]if idx>=0 and hit.start()<ts[idx]['end']else None
  lineno=bisect.bisect_right(line_starts,hit.start())
  linebody=t[line_starts[lineno-1]:line_starts[lineno]if lineno<len(line_starts)else len(t)]
  index[base].append(dict(path=path,line=lineno,offset=hit.start(),caller=owner['name']if owner else None,diagnostic=linebody.lstrip().startswith('#print')))
entries=[]
for mod in modules:
 p=B/(mod+'.lean');s,ds=parsed[str(p)]
 for d in ds:
  name=d['name'];base=name.split('.')[-1];refs=[];diagnostics=[]
  for x in index[base]:
   path=x['path'];offset=x['offset']
   if d['private']and path!=str(p):continue
   if path==str(p)and d['start']<=offset<s.find('\n',d['start']):continue
   if x['diagnostic']:
    diagnostics.append(dict(path=path,line=x['line']));continue
   refs.append(dict(path=str(Path(path).relative_to(ROOT)),line=x['line'],caller=x['caller'],self_reference=path==str(p)and x['caller']==name))
  callers=sorted({(x['path'],x['caller'])for x in refs if not x['self_reference']},key=str)
  entries.append({k:v for k,v in d.items()if k not in ('text','start','end')}|dict(module=mod,reference_occurrences=len(refs),caller_declarations=len(callers),references=refs,diagnostic_references=diagnostics,scope='exact private-name lexical scope'if d['private']and'.'not in name else'conservative basename tokens; possible collisions/unresolved dot notation'))
result=dict(status='SOURCE_ONLY_CONSERVATIVE_CENSUS',modules=modules,inputs=[pin(B/(x+'.lean'))for x in modules],maintained_files_scanned=len(parsed),declarations=entries,compiler_invocations=[],canonical_mutations=[])
(OUT/'census.json').write_text(json.dumps(result,indent=2)+'\n')
for e in entries:
 if e['kind']in ('theorem','lemma')and e['caller_declarations']<=1:
  print(f"{e['module']:23} {e['name']:30} {'private'if e['private']else'public ':7} {e['lines']:3}lines {e['bytes']:4}B refs{e['reference_occurrences']:2} callers{e['caller_declarations']} " +str([(x['caller'],x['line'])for x in e['references'] if not x['self_reference']]))
