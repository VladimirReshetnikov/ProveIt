from pathlib import Path
import json,zipfile,hashlib,re
p=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261028-peel-sharing-deferred-evidence');note=Path('Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-28-peel-sharing-deferred.md').read_text();j=json.loads((p/'BUNDLE.json').read_text());h=lambda b:hashlib.sha256(b).hexdigest();arc=p/j['archive'];assert h(arc.read_bytes())==j['archive_sha256'];pre='peel-sharing-deferred-evidence-20261028/'
with zipfile.ZipFile(arc) as z:
 assert z.testzip() is None and set(z.namelist())==set(j['members'])
 for n,v in j['members'].items():
  b=z.read(n);assert h(b)==v['sha256'] and len(b)==v['bytes']
 manifest=z.read(pre+'manifest.sha256').decode().splitlines()
 for line in manifest:
  digest,n=line.split('  ',1);assert h(z.read(pre+n))==digest
 assert len(manifest)+1==len(z.namelist())
 for n in z.namelist():
  content=z.read(n);assert b'\x00' not in content;content.decode('utf-8')
 bad=[x for x in z.namelist() if x.endswith(('.olean','.ilean','.o','.a','.so','.dll','.exe','.pyc','.bc'))];assert not bad
 def text(n):return z.read(pre+n).decode()
 archived=text('records/research-note.txt');assert note.startswith('# '+archived.splitlines()[0].removesuffix(', 28 October 2026')+'\n') and archived.split('\n',1)[1].strip() in note and '[Evidence bundle](../../reviews/lean-proof-simplification-20261028-peel-sharing-deferred-evidence/BUNDLE.json)' in note
 src='DiophantineConsistency/ArithmeticRuntimeBoundTapeSymbolic.lean';a=text('sources/baseline/'+src);b=text('sources/final/'+src);assert len(a.splitlines())-len(b.splitlines())==3
 left='lemma peelLeft_actualB ';right='lemma peelRight_actualB ';suffix='/-- `sstep_actual`';assert a[:a.index(left)]==b[:b.index('/-- Peeling a run has the same proof')];assert a[a.index(suffix):]==b[b.index(suffix):]
 for label in (left,right):assert a[a.index(label):a.index(' := by',a.index(label))]==b[b.index(label):b.index(' := by',b.index(label))]
 def names(ph):return {line[5:] for line in text('records/'+ph+'-names.log').splitlines() if line.startswith('DECL ')}
 aa,bb=names('baseline'),names('final');removed=aa-bb;added=bb-aa;assert len(removed)==11 and len(added)==12 and sum(n.startswith('_private.') for n in added)==10 and all(not n.startswith('_private.') for n in removed)
 assert set(text('records/removed-names.txt').splitlines())==removed
 simp1=text('records/baseline-global-simp.log');simp2=text('records/final-global-simp.log');inst1=text('records/baseline-instances.log');inst2=text('records/final-instances.log');assert simp1==simp2 and inst1==inst2 and len(simp1.splitlines())==29211 and len(inst1.splitlines())==13320
 changed=text('records/changed-common-names.txt').splitlines();assert len(changed)==14 and all(n in aa&bb and n not in simp1 and n not in inst1 for n in changed) and all(n not in simp1 and n not in inst1 for n in removed)
 diff=text('records/interfaces.diff');lines=text('records/interfaces.lean').splitlines();nums=sorted(set(map(int,re.findall(r'interfaces\.lean:(\d+):',diff))));assert {lines[i-1].removeprefix('#check ') for i in nums}==set(changed)
 for x in json.loads(text('records/reference-search-records.json')):
  assert x['status']==1 and x['bytes']==0 and x['command'][-2:]==['Computability/DiophantineConsistency','Computability/BusyBeaver'];assert h(z.read(pre+'records/'+Path(x['terms']).name))==x['terms_before']==x['terms_after'];assert h(z.read(pre+'records/'+Path(x['log']).name))==x['log_sha256']
 builds={ph:json.loads(text('records/'+ph+'-records.json')) for ph in ('baseline','final')}
 for ph,xs in builds.items():
  assert len(xs)==3 and all(x['status']==0 and x['before']==x['after'] for x in xs)
  for x in xs:
   sb=z.read(pre+'sources/'+ph+'/DiophantineConsistency/'+x['module']+'.lean');assert h(sb)==x['before']
 for i in (1,2):assert builds['baseline'][i]['object_sha256']==builds['final'][i]['object_sha256']
 f=json.loads(text('records/initial-failed-records.json'))[0];assert f['status']!=0 and h(z.read(pre+'records/initial-failed.lean'))==f['before']==f['after'] and h(z.read(pre+'records/initial-failed.log'))==f['log_sha256'] and h(z.read(pre+'records/initial-failed.time'))==f['time_sha256']
 print('CRC and archive SHA verified; BUNDLE entries',len(j['members']),'and inner manifest',len(manifest),'verified; all members UTF-8 text without NUL, known compiled artifact suffixes absent')
 print('Research note agrees with archived note; claims checked against source, six build records, name/type/simp/instance logs and two limited search receipts')
 print('scope limitation: no validation of arbitrary unknown binary formats, external consumers, or entire cached dependency closure')
 print('archive SHA256',j['archive_sha256'])
