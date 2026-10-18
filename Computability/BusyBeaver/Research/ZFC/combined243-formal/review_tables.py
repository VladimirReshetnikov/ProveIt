#!/usr/bin/env python3
"""Independent literal parser for generated table sources; never invokes Lean."""
from pathlib import Path
import hashlib,json,re,ast
B=Path('/tmp/zfc243-combined-lean')
count=0
def check(v):
 global count
 assert v
 count+=1
def d(p):return {'path':str(p),'sha256':hashlib.sha256(Path(p).read_bytes()).hexdigest()}
def read_table(p):
 rows={}
 for l in Path(p).read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,move,t=l.split();rows[int(q),int(b)]=(int(w),move,int(t))
 return rows
def parse_source(text,n):
 rowpat=r'^  \(\((true|false), \.(left|right), (\d+)\), \((true|false), \.(left|right), (\d+)\)\),? -- (\d+); old(\d+)$'
 rr=re.findall(rowpat,text,re.M);check(len(rr)==n)
 rows={};labels=[]
 for i,(b0,m0,t0,b1,m1,t1,q,old) in enumerate(rr):
  check(int(q)==i);labels.append(int(old))
  rows[i,0]=(int(b0=='true'),'L' if m0=='left' else 'R',int(t0))
  rows[i,1]=(int(b1=='true'),'L' if m1=='left' else 'R',int(t1))
 mappings={int(a):int(b) for a,b in re.findall(r'^  \| (\d+) => (\d+)$',text,re.M)}
 check(mappings=={old:i for i,old in enumerate(labels)})
 return rows,labels,mappings
units=[];sources={};oldtables={};maps={}
for folder,name,n,census in [('table-rotation','TableRotation244',244,(7,7)),('table-combined','TableCombined243',243,(53,6))]:
 p=B/folder;inv=json.loads((p/'source-inventory.json').read_text());s=p/(name+'.lean');a=p/'Audit.lean'
 check(inv['source']==d(s) and inv['audit']==d(a))
 for x in inv['inputs']+[inv['generator']]:check(d(x['path'])==x)
 text=s.read_text();sources[name]=text
 rows,labels,mapping=parse_source(text,n)
 canonical=read_table(inv['inputs'][0]['path']);old=read_table(inv['inputs'][1]['path']);ren=json.loads(Path(inv['inputs'][2]['path']).read_text())
 check(rows==canonical and labels==ren['canonical_to_old'])
 check(mapping=={int(k):v for k,v in ren['old_to_canonical'].items() if int(k)!=254})
 for (q,b),(w,m,t) in old.items():check(rows[mapping[q],b]==(w,m,n if t==254 else mapping[t]))
 check(labels[0]==95 and mapping[96]==87 and {k for k,v in old.items() if v[2]==254}=={(77,1)})
 check(old[77,1]==(1,'R',254))
 check(not re.search(r'\b(sorry|axiom|native_decide|set_option)\b',text))
 probes=re.findall(r'^#print axioms (\S+)$',a.read_text(),re.M)
 check((len(probes),len(re.findall(r'^example\b',a.read_text(),re.M)))==census)
 check(all(x.startswith('SetTheory.BusyBeaver.ZFC.') for x in probes))
 declarations=set(re.findall(r'^theorem (\w+)',text,re.M));check({x.rsplit('.',1)[1] for x in probes}<=declarations)
 units.append({'source':d(s),'audit':d(a),'inventory':d(p/'source-inventory.json'),'probes':census[0],'callers':census[1],'actions':2*n})
 oldtables[name]=old;maps[name]=mapping
rot=oldtables['TableRotation244'];com=oldtables['TableCombined243'];rm=maps['TableRotation244'];cm=maps['TableCombined243']
check(rm[122]==112)
check(all(rm[q]==(i if i<112 else i+1) for q,i in cm.items()))
for text in sources.values():
 for which,q,b,w,move,t in re.findall(r'theorem foldRow(Rotation244|Combined243)_old(\d+)_(true|false) :\s*machine\1.transition \(oldState\1 \2\) \3 =\s*⟨(true|false), \.(left|right), some \(oldState\1 (\d+)\)⟩',text):
  check(oldtables['Table'+which][int(q),int(b=='true')]==(int(w=='true'),'L' if move=='left' else 'R',int(t)))
common=0
for key,row in com.items():
 if key[0]!=92 and key not in {(81,1),(104,1),(106,1),(167,1)}:
  check(row==rot[key] and row[2]!=92);common+=1
check(common==480)
port=json.loads((B/'source-inventory.json').read_text())
declared=set(re.findall(r'^(?:theorem|def) (\w+)','\n'.join(sources.values()),re.M))
check(set(port['expected_table_api'])<=declared)
check('embedConfig243 (initial 243) = initial 244 := by\n  rfl' in sources['TableCombined243'])
record={'status':'SOURCE_ONLY_TABLE_REVIEW_PASS','findings':[],'units':units,'reviewer_source':d(__file__),'checks':count,
 'read_scope':'Full generator, both source definitions and theorem tails, complete audits, and every literal action/old-label mapping parsed independently. No compiler or supplied generator executed.',
 'conclusions':['Exact488 Rotation actions and486 Combined actions agree with frozen candidate tables.','Embedding skips Rotation canonical112, exactly old122.','All local row facts,480 ordinary-action rows, checkpoint exclusions, and dependent-port API names agree.','No source/runtime/calibration or PA endpoint follows from table facts alone.'],
 'reviewer_role':'Independent table-source reviewer; author of dependent invariant/blocks/simulation ports, not table generator or table proof runner.'}
(B/'independent-table-source-review.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(d(B/'independent-table-source-review.json')))
