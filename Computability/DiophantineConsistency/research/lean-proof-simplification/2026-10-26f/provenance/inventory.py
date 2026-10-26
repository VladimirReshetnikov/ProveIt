#!/usr/bin/env python3
"""Reproducible lexical inventory; not a Lean parser or proof checker."""
import json,pathlib,re,collections,csv,hashlib
BASE=pathlib.Path(__file__).resolve().parents[1]; ROOT=BASE/'sources/Computability/DiophantineConsistency/Lean'; OUT=BASE/'inventory';OUT.mkdir(exist_ok=True)
def no_comments(s):
 out=[];i=0;depth=0;instr=False
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;out.extend('  ');i+=2
   elif s.startswith('-/',i):depth-=1;out.extend('  ');i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif instr:
   if s[i]=='\\':out.extend('  ');i+=2
   elif s[i]=='"':instr=False;out.append(' ');i+=1
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s.startswith('--',i):
   j=s.find('\n',i);j=len(s) if j==-1 else j;out.extend(' '*(j-i));i=j
  elif s.startswith('/-',i):depth=1;out.extend('  ');i+=2
  elif s[i]=='"':instr=True;out.append(' ');i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)
rows=[];decls=[];edge=[];patterns=['simp','simp_all','simpa','rw','omega','ring','ring_nf','linarith','nlinarith','norm_num','decide','native_decide','fin_cases','ext','funext','aesop','exact','rfl','sorry','axiom']
for p in sorted(ROOT.rglob('*.lean')):
 raw=p.read_text();s=no_comments(raw);rel=p.relative_to(ROOT).as_posix(); code_lines=sum(bool(l.strip()) for l in s.splitlines());imports=re.findall(r'^import\s+(\S+)',s,re.M)
 group='checks' if rel.startswith('checks/') else ('umbrella' if '/' not in rel else 'modules')
 isgen=bool(re.search(r'generated (?:by|from|file)|auto[- ]generated|automatically generated',raw[:1500],re.I))
 role = 'check_or_audit' if group=='checks' or p.stem.endswith(('Checks','Audit','Axioms')) else ('umbrella' if group=='umbrella' else 'implementation')
 row=dict(path=rel,group=group,role=role,bytes=p.stat().st_size,lines=len(raw.splitlines()),code_lines=code_lines,generated_header=isgen,imports=len(imports),theorems=len(re.findall(r'^\s*(?:(?:private|protected|noncomputable)\s+)?(?:theorem|lemma)\s',s,re.M)),definitions=len(re.findall(r'^\s*(?:(?:private|protected|noncomputable)\s+)?(?:def|abbrev)\s',s,re.M)),axiom_prints=len(re.findall(r'#print\s+axioms\b',s)),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
 for k in patterns:row[k]=len(re.findall(r'(?<![\w.])'+k+r'\b',s))
 rows.append(row)
 module=rel[:-5].replace('/','.')
 for imp in imports:edge.append({'module':module,'import':imp,'local':imp=='DiophantineConsistency' or imp.startswith('DiophantineConsistency.')})
 matches=list(re.finditer(r'^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)?(theorem|lemma|def|abbrev|structure|inductive)\s+([^\s(:{]+)',s,re.M))
 for i,m in enumerate(matches):
  end=matches[i+1].start() if i+1<len(matches) else len(s)
  a=s.count('\n',0,m.start())+1;b=s.count('\n',0,end)
  decls.append({'path':rel,'kind':m.group(1),'name':m.group(2),'start_line':a,'next_declaration_line':b+1,'span_lines':b-a+1,'group':group,'generated_header':isgen})
for filename, rr in [('modules.csv',rows),('declaration_spans.csv',decls),('imports.csv',edge)]:
 with open(OUT/filename,'w') as f:
  w=csv.DictWriter(f,rr[0].keys());w.writeheader();w.writerows(rr)
summary={'scope':'Lean/ only; excludes archived con-zfc-diophantine-forms and candidates','method':'Lexical counts with nested block comments, line comments, and string literals removed; declaration spans are estimates extending to next declaration, not exact proof-body lengths. generated_header is conservative header heuristic, not exhaustive.','groups':{},'roles':{},'tokens':{},'generated_header_files':[r['path'] for r in rows if r['generated_header']]}
for g in ['modules','umbrella','checks']:
 rr=[r for r in rows if r['group']==g];summary['groups'][g]={k:sum(r[k] for r in rr) for k in ['bytes','lines','code_lines','theorems','definitions','axiom_prints']};summary['groups'][g]['files']=len(rr)
for role in ['implementation','umbrella','check_or_audit']:
 rr=[r for r in rows if r['role']==role];summary['roles'][role]={k:sum(r[k] for r in rr) for k in ['bytes','lines','code_lines','theorems','definitions','axiom_prints']};summary['roles'][role]['files']=len(rr)
summary['role_method']='Filename/directory classification: check_or_audit if under checks/ or basename ends Checks, Audit, or Axioms; implementation otherwise except umbrella. Not a semantic proof classifier.'
for k in patterns:summary['tokens'][k]=sum(r[k] for r in rows if r['group']=='modules')
summary['top_internal_fanin']=collections.Counter(e['import'] for e in edge if e['local'] and not e['module'].startswith('checks.') and e['module']!='DiophantineConsistency').most_common(25)
summary['top_external_imports']=collections.Counter(e['import'] for e in edge if not e['local']).most_common()
(OUT/'summary.json').write_text(json.dumps(summary,indent=2))
print(json.dumps(summary,indent=2))
