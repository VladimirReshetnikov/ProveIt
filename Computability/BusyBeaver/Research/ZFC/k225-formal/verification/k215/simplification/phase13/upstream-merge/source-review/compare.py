from pathlib import Path
import subprocess,re,json,hashlib
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');O=Path('/tmp/k215-upstream565-review');M=json.loads((O/'preservation-map.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
changes=M['rows'][:4]; removed=['h0','h1','h2','thm_of_der0','ded1','ded2','ded3','syl','contra_thm','contra','dne','dni','imp_cases','all_mono','ex_mono','ex_elim_of_vac','vac_neg','rel_L','rel_R','atom_subst','atom_subst_rev','all_imp_ex']
sourcepins=json.loads(Path('/tmp/k215-phase13-root/current-review.json').read_text())['sources']
proofbindings=[];metrics=[];headers={}
# This is a lexical declaration comparison, not a Lean parser or kernel check.
start=re.compile(r'(?m)^(?:(?:private|protected|noncomputable)\s+)?(?:theorem|def|class|structure|inductive)\s+([A-Za-z0-9_]+)')
def decls(t):
 hits=list(start.finditer(t));res={}
 for i,h in enumerate(hits):
  block=t[h.start():hits[i+1].start() if i+1<len(hits) else len(t)]
  sig=block.split(':=',1)[0].split('\n  |',1)[0]
  res[h.group(1)]=' '.join(sig.split())
 return res
for row in changes:
 mod='BusyBeaver.ZFC.'+Path(row['path']).stem
 a=Path(row['checked_worktree']['snapshot']).read_text();b=Path(row['upstream']['snapshot']).read_text()
 assert sourcepins[mod]['sha256']==row['checked_worktree']['sha256']
 proofbindings.append({'module':mod,'phase13_sha256':sourcepins[mod]['sha256'],'current_sha256':sha((R/row['path']).read_bytes())})
 ia=re.findall(r'(?m)^import (.*)$',a);ib=re.findall(r'(?m)^import (.*)$',b);assert ia==ib
 x,y=decls(a),decls(b)
 metrics.append({'module':mod,'before_bytes':len(a.encode()),'upstream_bytes':len(b.encode()),'before_lines':len(a.splitlines()),'upstream_lines':len(b.splitlines()),'imports_unchanged':ia,'removed_declarations':[n for n in x if n not in y],'added_declarations':[n for n in y if n not in x]})
 headers[mod]={'unchanged':[n for n in x if n in y and x[n]==y[n]],'changed':{n:{'before':x[n],'upstream':y[n]} for n in x if n in y and x[n]!=y[n]}}
 if mod.endswith('KEind222'):assert x==y
 if mod.endswith('KThmK'):assert all(x[n]==y[n] for n in y if n in x)
paths=subprocess.check_output(['git','ls-files','-z','--','*.lean'],cwd=R).decode().split('\0');paths=[p for p in paths if p]
quals=re.compile(r'\bKThmK\.('+'|'.join(map(re.escape,removed))+r')\b')
kw=re.compile(r'\b(?:rel_L|rel_R|eq_L|all_mono|ex_mono|ded1|ded2|ded3|syl|dne|dni|h0|h1|h2)\s*\(\s*Ax\s*:=')
main=[];historical=[];kwmain=[];reversecalls=[];kopens=[]
for rel in paths:
 p=R/rel
 if not p.exists():continue
 t=p.read_text(errors='replace')
 found=[{'line':t.count('\n',0,m.start())+1,'name':m.group(0)} for m in quals.finditer(t)]
 maintained=rel.startswith('Computability/BusyBeaver/Lean/')
 if found:(main if maintained else historical).append({'path':rel,'matches':found})
 if maintained and rel not in [r['path'] for r in changes]:
  for m in kw.finditer(t):kwmain.append({'path':rel,'line':t.count('\n',0,m.start())+1,'text':m.group(0)})
  for m in re.finditer(r'\batom_subst_rev\b',t):reversecalls.append({'path':rel,'line':t.count('\n',0,m.start())+1})
  if re.search(r'\bopen\b[^\n]*\bKThmK\b',t):kopens.append(rel)
assert not main and not kwmain and not reversecalls
invs={name:json.loads((Path('/tmp/k215-phase13-upstream-check')/(name+'-run1')/'inventory.json').read_text()) for name in ['primary','compatibility']}
roots={}
changed={x['module'] for x in metrics}
for name,inv in invs.items():
 graph={x['module']:x['imports'] for x in inv['modules']};memo={}
 def affected(n):
  if n not in graph:return False
  if n not in memo:memo[n]=n in changed or any(affected(i) for i in graph[n])
  return memo[n]
 force=[n for n in graph if affected(n)]
 roots[name]={'providers':len(graph),'changed_source_descendants':force,'count':len(force),'fresh_site_batches':[n for n in force if 'KSites215Batch' in n]}
record={'status':'READ_ONLY_API_AND_CURRENT_BINDING_CENSUS','phase13_current_review_sha256':sha(Path('/tmp/k215-phase13-root/current-review.json').read_bytes()),'four_current_bindings':proofbindings,'metrics':metrics,'before_total_bytes':sum(x['before_bytes'] for x in metrics),'upstream_total_bytes':sum(x['upstream_bytes'] for x in metrics),'before_total_lines':sum(x['before_lines'] for x in metrics),'upstream_total_lines':sum(x['upstream_lines'] for x in metrics),'lexical_headers':headers,'tracked_lean_files_scanned':len(paths),'maintained_qualified_removed_callers':main,'maintained_outside_delta_ax_keyword_callers':kwmain,'maintained_outside_delta_atom_subst_rev_callers':reversecalls,'maintained_outside_delta_same_line_KThmK_opens':kopens,'nonmaintained_qualified_removed_callers':historical,'unchanged_import_closure_affected_counts':roots,'scope':'Lexical source census and graph arithmetic, not elaboration. Archived snapshots/typed records are historical data; public API changes remain real even when no maintained caller uses the removed namespace.'}
(O/'comparison.json').write_text(json.dumps(record,indent=2)+'\n')
print('metrics',record['before_total_bytes'],record['upstream_total_bytes'],record['before_total_lines'],record['upstream_total_lines'])
print('tracked_lean',len(paths),'qualified_removed',len(main),'historical_matches',len(historical),'outside_ax',len(kwmain),'outside_reverse',len(reversecalls),'opens',kopens)
print('graph',{n:(q['providers'],q['count'],q['fresh_site_batches']) for n,q in roots.items()})
print('comparison_sha256',sha((O/'comparison.json').read_bytes()))
