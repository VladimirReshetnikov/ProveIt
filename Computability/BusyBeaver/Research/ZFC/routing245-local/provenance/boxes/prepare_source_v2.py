"""Remove only seven actually reported unused simp arguments; no proof call."""
from pathlib import Path
import ast,difflib,hashlib,json,shutil,re
B=Path('/tmp/zfc-routing245-lean/boxes');h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();desc=lambda p:dict(path=str(p),sha256=h(p))
source=B/'Routing245Boxes.lean';guard=B/'check-v2.py';audit=B/'Audit.lean';record=B/'run1/verification.json';log=B/'run1/source.log'
assert h(source)=='a9fc8de314aad422101ddc492044da1dbfd146dbd17cb119cc836e1c00a47de4'
assert h(guard)=='c89dbf854f3144881f4240df7178a8c8887e55b616719d61e27413003f8a08f1'
assert h(record)=='fec29e132eca9473581798977941bfc83ad1e2a9f1513529753d8af3b8e40e0c'
d=json.loads(record.read_text());assert d['status']=='PASS'and d['warnings']=={'source':7,'audit':0}
reported=re.findall(r'\.lean:(\d+):\d+: warning: This simp argument is unused:\n  ([\w.]+)',log.read_text())
assert reported==[('162','List.cons_append'),('162','List.append_assoc'),('229','List.cons_append'),('229','List.append_assoc'),('324','List.cons_append'),('324','List.append_assoc'),('361','List.nil_append')]
history=B/'history/attempt1-before-warning-cleanup';assert not history.exists();history.mkdir(parents=True)
for p in [source,audit,guard,record,log,B/'run1/audit.log',B/'source-guard-inventory.json',B/'pulse-parent-freeze.json']:
 dest=history/p.relative_to(B);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest);assert p.read_bytes()==dest.read_bytes()
old=source.read_text();lines=old.splitlines(True)
for lineno,names in [(162,['List.cons_append','List.append_assoc']),(229,['List.cons_append','List.append_assoc']),(324,['List.cons_append','List.append_assoc']),(361,['List.nil_append'])]:
 for name in names:
  assert lines[lineno-1].count(name)==1
  if ', '+name in lines[lineno-1]:lines[lineno-1]=lines[lineno-1].replace(', '+name,'',1)
  else:raise AssertionError('Expected comma-prefixed simp argument')
new=''.join(lines);out=B/'source-v2/Routing245Boxes.lean';assert not out.parent.exists();out.parent.mkdir();out.write_text(new)
oldguard=guard.read_text();newguard=oldguard.replace(h(source),h(out)).replace(str(source),str(out))
assert oldguard.count(h(source))==1 and oldguard.count(str(source))==1
assert newguard.replace(h(out),h(source)).replace(str(out),str(source))==oldguard;ast.parse(newguard)
nextguard=B/'check-v3.py';assert not nextguard.exists();nextguard.write_text(newguard)
(B/'source-warning-cleanup.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=str(source),tofile=str(out))))
(B/'guard-warning-cleanup.diff').write_text(''.join(difflib.unified_diff(oldguard.splitlines(True),newguard.splitlines(True),fromfile=str(guard),tofile=str(nextguard))))
r=dict(status='SOURCE_ONLY_SEVEN_UNUSED_SIMP_ARGUMENTS_REMOVED',successful_prior_record=desc(record),prior_source=desc(source),source=desc(out),audit=desc(audit),prior_guard=desc(guard),guard=desc(nextguard),removed_arguments=[dict(line=int(n),argument=a)for n,a in reported],history=str(history),public_statements_unchanged=True,no_linter_disables=True,no_budget_changes=True,guard_delta='Source digest and source default path only.',proof_execution=False,guard_execution=False)
(B/'source-warning-cleanup.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
