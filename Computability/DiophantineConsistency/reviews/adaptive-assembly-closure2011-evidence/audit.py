from pathlib import Path
import hashlib,json,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');S=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency';A=Path('/tmp/adaptive13-ranklower-postmerge-tjqelwlk/lib/DiophantineConsistency');B=Path('/tmp/construction-share/pinned-final/DiophantineConsistency');seen=set();order=[];edges={}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def visit(n):
 if n in seen:return
 seen.add(n);p=S/(n+'.lean');assert p.is_file(),p
 imports=re.findall(r'^import\s+([\w.]+)',p.read_text(),re.M);edges[n]=imports
 for m in imports:
  if m.startswith('DiophantineConsistency.'):
   child=m.split('.',1)[1]
   if (S/(child+'.lean')).is_file():visit(child)
 order.append(n)
visit('ArithmeticConstructionAssembly');rows=[];different=set();oldonly=set();newonly=set()
for n in order:
 a=A/(n+'.olean');b=B/(n+'.olean');ha=sha(a) if a.is_file() else None;hb=sha(b) if b.is_file() else None
 if ha and hb and ha!=hb:different.add(n)
 if hb and not ha:oldonly.add(n)
 if ha and not hb:newonly.add(n)
 rows.append({'module':n,'imports':edges[n],'source_sha256':sha(S/(n+'.lean')),'current_object_sha256':ha,'historical_object_sha256':hb,'current_object':str(a.resolve()) if ha else None,'historical_object':str(b.resolve()) if hb else None})
affected=set(different)|set(newonly)
for n in order:
 if any(i.startswith('DiophantineConsistency.') and i.split('.',1)[1] in affected for i in edges[n]):affected.add(n)
external=sorted({i for v in edges.values() for i in v if not i.startswith('DiophantineConsistency.')})
out={'scope':'DiophantineConsistency imports in current Assembly source closure only; cross-namespace dependencies recorded but not recursively audited','current_provider':str(A.parent),'historical_provider':str(B.parent),'order':order,'different_overlap':sorted(different),'old_only_refresh':[n for n in order if n in oldonly and n in affected],'old_only_other':[n for n in order if n in oldonly and n not in affected],'current_only':sorted(newonly),'external_imports':external,'rows':rows};Path('/tmp/adaptive-assembly-closure-audit.json').write_text(json.dumps(out,indent=2)+'\n');print('nodes',len(order),'differ',len(different),'old-only affected',len(out['old_only_refresh']),'old-only other',len(out['old_only_other']),'external',len(external));print('old-only affected order:');print('\n'.join(out['old_only_refresh']));print('old-only other:',out['old_only_other']);print('external:',external)
