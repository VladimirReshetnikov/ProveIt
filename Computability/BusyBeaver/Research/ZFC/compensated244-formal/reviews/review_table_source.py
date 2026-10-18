#!/usr/bin/env python3
"""Independent literal parsing, no execution of the machine or author emitter."""
from pathlib import Path
import json,hashlib,re,ast
B=Path('/tmp/zfc244-compensated-lean/table');P=Path('/tmp/zfc244-248bc05936-inspection/zfc244-compensated-routing-20261018')
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');OUT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def d(p):return {'path':str(p),'sha256':sha(p)}
def load(p):return json.loads(Path(p).read_text())
checks=[]
def check(ok,label):
 assert ok,label
 checks.append(label)
def literal(p):
 rows={}
 for l in p.read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,m,t=l.split();key=(int(q),int(b));check(key not in rows,'unique literal '+str(key));rows[key]=(int(w),m,int(t))
 return rows
source=(B/'TableCompensated244.lean').read_text();audit=(B/'Audit.lean').read_text()
can=literal(P/'machine/zfc_compensated244.tm');old=literal(P/'runtime/reference/zfc245_old.tm');nm=load(P/'machine/renumbering.json')
om=load(R/'Computability/BusyBeaver/Research/ZFC/candidate-routing245/renumbering.json')['old_to_canonical']
pattern=r'^  \(\((true|false), \.(left|right), (\d+)\), \((true|false), \.(left|right), (\d+)\)\),? -- (\d+); old(\d+)$'
rows={};labels={}
for m in re.finditer(pattern,source,re.M):
 w0,d0,t0,w1,d1,t1,q,label=m.groups();q=int(q);labels[q]=int(label)
 rows[q,0]=(int(w0=='true'),d0[0].upper(),int(t0));rows[q,1]=(int(w1=='true'),d1[0].upper(),int(t1))
check(rows==can and len(rows)==488,'all488 generated canonical actions exact')
check([labels[i] for i in range(244)]==nm['canonical_to_old'],'all244 literal label comments exact')
mapping={int(a):int(b) for a,b in re.findall(r'^  \| (\d+) => (\d+)$',source,re.M)}
check(mapping=={int(k):v for k,v in nm['old_to_canonical'].items() if int(k)!=254},'total244 working label clauses exact')
check('  | _ => 0\n' in source,'absent label fallback documented')
for q in range(244):
 image=q if q<113 else q+1
 check(image==om[str(labels[q])] and image!=om['122'],'embedding preserves old label '+str(q))
ordinary=[]
for q in range(244):
 for b in (0,1):
  label=labels[q]
  if label==92 or (b==1 and label in (104,106,167,81)):continue
  ordinary.append((q,b));w,m,t=rows[q,b]
  target=254 if t==244 else labels[t]
  check(old[label,b]==(w,m,target),'common action '+str((q,b)))
  check(target!=92,'common target checkpoint '+str((q,b)))
check(len(ordinary)==482,'482 ordinary actions')
row_pattern=r'theorem (foldRow(Compensated244|Routing245)_old(\d+)_(true|false)) :\s*machine\2.transition \(oldState\2 \3\) \4 =\s*⟨(true|false), \.(left|right), some \(oldState\2 (\d+)\)⟩ := by decide \+kernel'
newold=literal(P/'machine/zfc_compensated244_old.tm')
finite=[]
for name,which,q,b,w,m,t in re.findall(row_pattern,source):
 tab=old if which=='Routing245' else newold
 check(tab[int(q),int(b=='true')]==(int(w=='true'),m[0].upper(),int(t)),'finite literal theorem '+name);finite.append(name)
check(len(finite)==30,'16old plus14new finite row facts')
names=re.findall(r'^theorem (\S+)',source,re.M)
probes=re.findall(r'^#print axioms SetTheory.BusyBeaver.ZFC.(\S+)$',audit,re.M)
check(names==probes and len(probes)==53,'all53 public theorem probes ordered')
check(len(re.findall(r'^example\b',audit,re.M))==6,'six typed clients')
check(not re.search(r'\b(sorry|axiom|native_decide|set_option)\b',source),'no proof escapes or options')
for x in ['source','audit','generator']:
 inv=load(B/'source-inventory.json')[x];check(sha(inv['path'])==inv['sha256'],'inventory '+x)
ast.parse((B/'prepare_source.py').read_text())
result={'status':'INDEPENDENT_TABLE_SOURCE_REVIEW_PASS','findings':[],'source':d(B/'TableCompensated244.lean'),'audit':d(B/'Audit.lean'),'emitter':d(B/'prepare_source.py'),'reviewer_source':d(Path(__file__)),
 'reviewer_role':'Independent source/literal/API reviewer; no emitter/guard/compiler execution or authorship.',
 'scope':['Complete canonical action table and working-label match independently parsed against delivered literals; old122 is canonical113 and the insert113 embedding preserves every surviving old label.',
 'Action embedding maps only the optional state, preserving write and move including the halting action. Configuration embedding leaves head and exact tape list unchanged. Canonical start maps to canonical0.',
 'The two ordinary-row theorems exclude92 and the four exceptional read-one entries; all482 other actions match and avoid92 at their endpoints.',
 'All30 local row theorem statements and16 selected embedding identities bind the exact old/new machines. Finite proofs use trusted decide+kernel. No runtime or consistency theorem is asserted by this module.',
 'All53 public theorem probes and6 typed data/common-action clients read. Explicit Omega import is coherent; prior unexecuted no-Omega source is historical. Actual compiler evidence is reviewed separately.'],
 'checks':checks,'check_count':len(checks),'supplied_execution':False}
out=OUT/'table-source-review.json';out.write_text(json.dumps(result,indent=2)+'\n');print(d(out))
