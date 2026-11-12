#!/usr/bin/env python3
"""Reproduce a source-only overlay and its lexical import inventory; never run Lean."""
from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parent
D=P.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
old_import=b'import DiophantineConsistency.Compact44.C44Short15Facts'
new_import=b'import CompactPortBoundsSlim'
old_ref=b'C44Short15Facts.port_bounds'
new_ref=b'CompactPortBoundsSlimDraft.port_bounds'
original=json.loads((D/'research/ordinary14-root78-endpoint-import-inventory/inventory.json').read_text())
rows=original['drafts_topological']
orig={r['module']:r for r in rows}
assert len(orig)==138
files={p.name[:-9]:p for p in (P/'source').glob('*.lean.src')}
assert set(files)==set(orig)|{'CompactPortBoundsSlim'}, (set(files)-set(orig),set(orig)-set(files))
helper=D/'research/ordinary14-compact-port-bounds-slim-draft/CompactPortBoundsSlim.lean'
assert files['CompactPortBoundsSlim'].read_bytes()==helper.read_bytes()
changed=[]; drafts={}; direct=set()
def imports(data):
 # Strip nested block and line comments while preserving line boundaries.
 # Header parsing is intentionally lexical and does not resolve Lean syntax.
 text=data.decode(); out=[]; i=0; depth=0
 while i<len(text):
  if depth:
   if text.startswith('/-',i):depth+=1;i+=2
   elif text.startswith('-/',i):depth-=1;i+=2
   else:
    if text[i]=='\n':out.append('\n')
    i+=1
  elif text.startswith('/-',i):depth=1;i+=2
  elif text.startswith('--',i):
   i=text.find('\n',i)
   if i<0:break
  else:out.append(text[i]);i+=1
 assert depth==0
 result=[]
 for line in ''.join(out).splitlines():
  s=line.strip()
  if not s:continue
  if s in ('prelude','module'):continue
  m=re.fullmatch(r'(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*)',s)
  if not m:break
  result.extend(m.group(1).split())
 return result

for module,row in orig.items():
 old=(D/row['path']).read_bytes()
 assert sha(old)==row['sha256'],module
 new=files[module].read_bytes()
 assert new==old.replace(old_import,new_import).replace(old_ref,new_ref),module
 assert old_import not in new and old_ref not in new
 imps=imports(new); bare=[x for x in imps if '.' not in x]; qual=[x for x in imps if '.' in x]
 drafts[module]={'path':'source/'+module+'.lean.src','source_path':row['path'],'source_sha256':sha(old),'overlay_sha256':sha(new),'bare_imports':bare,'qualified_imports':qual}
 direct.update(qual)
 if old!=new:
  changed.append({'module':module,'import_replacements':old.count(old_import),'reference_replacements':old.count(old_ref),'old_bytes':len(old),'new_bytes':len(new),'source_sha256':sha(old),'overlay_sha256':sha(new)})
hdata=helper.read_bytes(); himps=imports(hdata); assert all('.' in x for x in himps)
drafts['CompactPortBoundsSlim']={'path':'source/CompactPortBoundsSlim.lean.src','source_path':str(helper.relative_to(D)),'source_sha256':sha(hdata),'overlay_sha256':sha(hdata),'bare_imports':[],'qualified_imports':himps};direct.update(himps)
assert len(changed)==6 and sum(x['import_replacements'] for x in changed)==4 and sum(x['reference_replacements'] for x in changed)==6
# Reachability includes the helper through the four explicit replacement imports.
order=[]; seen=set(); active=set()
def visit(m):
 assert m in drafts,('missing bare module',m)
 if m in seen:return
 assert m not in active,('cycle',m)
 active.add(m)
 for x in drafts[m]['bare_imports']:visit(x)
 active.remove(m);seen.add(m);order.append(m)
visit('Root78Endpoint')
assert set(order)==set(drafts),set(drafts)-set(order)
def reaches_helper(m, seen=None):
 if m=='CompactPortBoundsSlim':return True
 seen=set() if seen is None else seen
 if m in seen:return False
 seen.add(m)
 return any(reaches_helper(x,seen) for x in drafts[m]['bare_imports'])
assert all(reaches_helper(x['module']) for x in changed)
assert b'namespace DiophantineConsistency.CompactPortBoundsSlimDraft' in hdata
assert b'theorem port_bounds ' in hdata
assert 'DiophantineConsistency.Compact44.C44Short15Facts' not in direct
# Traverse initial import headers of reachable project sources, excluding external
# modules. This is a lexical source view, not Lean's dependency computation.
project={}; external=set(); pending=sorted(direct,reverse=True)
while pending:
 name=pending.pop()
 if name in project or name in external:continue
 p=D/'Lean'/('/'.join(name.split('.'))+'.lean')
 if not p.is_file():external.add(name);continue
 data=p.read_bytes(); imps=imports(data)
 project[name]={'path':str(p.relative_to(D)),'sha256':sha(data),'imports':imps}
 pending.extend(imps)
assert 'DiophantineConsistency.Compact44.C44Short15Facts' not in project
result={'scope':'static initial import headers only; overlay materialization, Lean elaboration, object/provider closure, model endpoint, physical bytes and PDF binding not verified','root':'Root78Endpoint','draft_count':len(order),'drafts_topological':[{'module':n,**drafts[n]} for n in order],'changed':sorted(changed,key=lambda x:x['module']),'direct_qualified_count':len(direct),'direct_qualified':sorted(direct),'project_source_count':len(project),'project_sources':dict(sorted(project.items())),'external_names_count':len(external),'external_names':sorted(external)}
print(json.dumps(result,sort_keys=True,indent=2))
