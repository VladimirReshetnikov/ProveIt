from pathlib import Path
import json,re,hashlib
P=Path(__file__).resolve().parent;R=Path('/home/codex/.codex/worktrees/ec20/Proofs');old=json.loads((P/'inventory-initial.json').read_text());by={x['module']:x for x in old['project_modules']}
roots=sorted({str(Path(x['relative_source']))[:-len(x['module'].replace('.','/')+'.lean')].rstrip('/')for x in old['project_modules']})
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def strip(s):
 out=[];i=0;d=0
 while i<len(s):
  if s[i:i+2]=='/-':d+=1;i+=2
  elif d and s[i:i+2]=='-/':d-=1;i+=2
  elif d:i+=1
  elif s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s)if j<0 else j
  elif s[i]=='"':
   i+=1
   while i<len(s):
    if s[i]=='\\':i+=2
    elif s[i]=='"':i+=1;break
    else:i+=1
  else:out.append(s[i]);i+=1
 assert d==0;return ''.join(out)
rows=[];seen=set();active=set();external={'Init'}
def visit(m):
 if m in seen:return
 assert m not in active,m
 pp=[R/r/(m.replace('.','/')+'.lean')for r in roots];found=[p for p in pp if p.is_file()]
 if not found:
  assert m=='Init' or m.startswith('Init.'),m
  external.add(m);return
 assert len(found)==1,(m,found);p=found[0];s=strip(p.read_text());imports=[x for z in re.findall(r'(?m)^\s*(?:public\s+)?import\s+([^\n]+)',s)for x in z.split()]
 if m in by and m!='BusyBeaver.ZFC.KSource215':assert imports==by[m]['imports'],(m,imports,by[m]['imports'])
 active.add(m)
 for x in imports:visit(x)
 active.remove(m);seen.add(m);rows.append(dict(module=m,relative_source=str(p.relative_to(R)),sha256=sha(p),imports=imports))
visit(old['target']);assert len(rows)==204,len(rows)
x=dict(toolchain=old['toolchain'],target=old['target'],order=[x['module']for x in rows],project_modules=rows,direct_external_imports=sorted(external),previous_inventory_sha256=sha(P/'inventory-initial.json'),reason='After actual monolith wall timeout, preserve all90 declarations in34 modules; adds33 project modules.')
(P/'inventory-v2.json').write_text(json.dumps(x,indent=2)+'\n');print(len(rows),sorted(external))
