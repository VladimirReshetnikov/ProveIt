from pathlib import Path
import subprocess,json,hashlib,re,runpy,difflib
O=Path('/tmp/gowers-incoming68ad-static-review');B='823ad7063d4f098246e204cea91f7756d5fe1aa3';L='5e5af281970d9f5c1ea637fa6b32fa7c4551a810';U='68ad8d39173bf0494fa46154869ccea9b1a3c623'
P=runpy.run_path('/tmp/gowers-equation-aware-scoped-parser/legacy-parsers.py');P['parse_declarations'].__globals__['COMMAND']=re.compile(P['COMMAND'].pattern.replace('|export|run_cmd','|export|alias|run_cmd'),re.M)
def git(*a):return subprocess.check_output(['git',*a],text=True)
def W(n,x):(O/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
files=git('diff','--name-only',B,U).splitlines();local=set(git('diff','--name-only',B,L).splitlines());future={x['file']:x for x in json.loads(Path('/tmp/gowers-next2090-prospective-composition/source-rows.json').read_text())}
(O/'incoming.patch').write_text(git('diff',B,U))
rows=[];removed=[];headers=[];imports=[];parsefails=[];conflicts=[]
for f in files:
 if not f.endswith('.lean'):continue
 b=git('show',B+':'+f);u=git('show',U+':'+f)
 bi=re.findall(r'^import\s+\S+',P['mask_comments'](b),re.M);ui=re.findall(r'^import\s+\S+',P['mask_comments'](u),re.M)
 if bi!=ui:imports.append(f)
 try:
  bd=P['declarations'](b);ud=P['declarations'](u)
  for n in bd.keys()-ud.keys():removed.append({'file':f,'name':n,'kind':bd[n]['kind'],'header':bd[n]['header'],'private':bool(re.search(r'\bprivate\b',bd[n]['header']))})
  for n in bd.keys()&ud.keys():
   if bd[n]['header']!=ud[n]['header'] or bd[n]['context']!=ud[n]['context']:headers.append({'file':f,'name':n,'before':bd[n]['header'],'after':ud[n]['header'],'context_before':bd[n]['context'],'context_after':ud[n]['context']})
  if ud.keys()-bd.keys():headers.append({'file':f,'added_names':sorted(ud.keys()-bd.keys())})
 except Exception as e:parsefails.append({'file':f,'error':str(e)})
 row={'file':f,'source_delta':len(u.splitlines())-len(b.splitlines()),'local_overlap':f in local,'next2090_overlap':f in future}
 if f in local:
  temp=O/'merge-comparison'/Path(f).stem;temp.mkdir(parents=True,exist_ok=True)
  for n,t in [('base',b),('local',git('show',L+':'+f)),('incoming',u)]: (temp/n).write_text(t)
  r=subprocess.run(['git','merge-file','-p','-L','LOCAL5e5a','-L','BASE823ad','-L','INCOMING68ad',str(temp/'local'),str(temp/'base'),str(temp/'incoming')],text=True,capture_output=True)
  assert r.returncode>=0 and not r.stderr,(f,r.returncode,r.stderr)
  row['read_only_merge_file_conflicts']=r.returncode
  if r.returncode:
   (temp/'conflicts.txt').write_text(r.stdout);conflicts.append({'file':f,'conflict_count':r.returncode,'comparison_path':str(temp/'conflicts.txt')})
 rows.append(row)
W('source-summary.json',rows);W('removed-declarations.json',removed);W('header-changes.json',headers);W('import-changes.json',imports);W('parse-limits.json',parsefails);W('local-conflicts.json',conflicts)
print(json.dumps({'lean_files':len(rows),'source_delta':sum(r['source_delta'] for r in rows),'removed_declarations':len(removed),'nonprivate_removed':[r for r in removed if not r['private']],'header_changes':headers,'parse_limits':parsefails,'import_changes':imports,'local_conflicts':conflicts,'future_overlap_count':sum(r['next2090_overlap'] for r in rows)},indent=2))
