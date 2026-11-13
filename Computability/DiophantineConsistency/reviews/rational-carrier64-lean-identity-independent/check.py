#!/usr/bin/env python3
"""Read-only literal-row transcription and retained Lean artifact review."""
import hashlib,json,os,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2]; p=r/'research/rational-carrier64-lean-identity';q=r/'research/rational-carrier64-independent';o=Path('/tmp/rational-carrier64-identity-priority-check03')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
pins={p/'RationalCarrier64.lean':'8676e328432ca3fd070dbd4abe6ae097137138aff4b2ceeead955e671f8b9a3b',p/'generate.py':'0da19fc7a5c175d5712a3e530363cd0f41965e9f73a6570729ad6ca4a8d67fde',q/'polynomial.json':'8fd205a43c4045914d88f4117ba263cf7a232ac26c64dcf09a1c37a8d88e7b27',q/'source/parent65.json':'408dde55352b837db3c606db446f3bf41dc7fd6d9242808ba4a123930bf0b5ff',p/'check03.py':'747de8d47715789be9727eb0ba5d4f7e6f830c36856c27972f30a12cd33ca574',p/'observations/attempt03/result.json':'daf3391dff8d54ceb64999b288cb6303046323733382777a680aa1e0996a86f3',p/'observations/attempt03/compile.log':'b1c3a224d14db8b6fb9aff207e9958407a69e2d670414dde9c05eef63e5a720a',o/'RationalCarrier64.olean':'a2aa0510f8dc710e455981b605c304c2a0dbfe75e343d443f33eac27aeef8b43',Path('/tmp/pell-class-simp-188/final/DiophantineConsistency/Carrier65.olean'):'50fcfd8fdc6a8abb6641a57e3fe2070dbab6c4d38ec28cf32f6e4e12caa89951'}
for f,h in pins.items():
 if not f.is_file() or sha(f)!=h:raise ValueError(('pin',str(f)))
d64=json.loads((q/'polynomial.json').read_bytes());d65=json.loads((q/'source/parent65.json').read_bytes());a=d64['source'];b=d65['source']
if len(a)!=64 or len(b)!=65 or d64['witnesses']!=d65['witnesses']:raise ValueError('graph inventory')
i=next(i for i,row in enumerate(a) if row[0]=='q2minus1'); j=next(i for i,row in enumerate(b) if row[0]=='q2minus1');e=next(i for i,row in enumerate(a) if row[0]=='R');f=next(i for i,row in enumerate(b) if row[0]=='R')
if a[:i]!=b[:j] or a[e+1:]!=b[f+1:]:raise ValueError('shared rows')
s=(p/'RationalCarrier64.lean').read_text()
def block(start,end):return s.split(start,1)[1].split(end,1)[0]
blocks={'head':block('def head ', '\ndef rank64 '),'rank64':block('def rank64 ','\ndef rank65 '),'rank65':block('def rank65 ','\ndef suffix '),'suffix':block('def suffix ','\ndef value64 ')}
segments={'head':a[:i],'rank64':a[i:e+1],'rank65':b[j:f+1],'suffix':a[e+1:]}
prefix_names={row[0] for row in a[:i]};ports={'beta':0,'K0':1,'MC':2,'MF':3};witness={name:k for k,name in enumerate(d64['witnesses'])}
for name,rows in segments.items():
 lets=re.findall(r'^  let (\w+) := (.+)$',blocks[name],re.M); names={x[0] for x in rows}; graphlets=[(k,v) for k,v in lets if k in names]; expected=[(k,f'{x} {op} {y}') for k,op,x,y in rows]
 if graphlets!=expected:raise ValueError(('row transcription',name))
 for key,expr in lets:
  if key in names:continue
  if key=='R' and name=='suffix' and expr=='rank':continue
  if key in ports and expr==f'p {ports[key]}':continue
  if key in witness and expr==f'v {witness[key]}':continue
  if key in prefix_names and expr==f'h.{key}':continue
  raise ValueError(('bad alias',name,key,expr))
 if len({k for k,_ in lets})!=len(lets):raise ValueError(('duplicate binding',name))
fields=re.findall(r'^  (\w+) : R$',block('structure Head ', '\ndef head '),re.M)
if fields!=[row[0] for row in a[:i]]:raise ValueError('head fields')
if '  ⟨'+', '.join(fields)+'⟩' not in blocks['head']:raise ValueError('head tuple')
for name in ('rank64','rank65'):
 if not blocks[name].rstrip().endswith('  R'):raise ValueError(('rank output',name))
if not blocks['suffix'].rstrip().endswith('  polynomial'):raise ValueError('suffix output')
if 'suffix p v h (rank64 h (v 0) Urank Wrank)' not in block('def value64 ','\ndef value65 '):raise ValueError('value64 wiring')
if 'suffix p v h (rank65 h (v 0) (p 2) (p 3))' not in block('def value65 ','\n/-- Pure'):raise ValueError('value65 wiring')
audit=json.loads((p/'observations/attempt03/result.json').read_bytes())
if audit['status']!='PASS' or audit['exit']!=0 or audit['stop_reason'] is not None or not audit['guards_stable'] or audit['guards_before']!=audit['guards_after'] or audit['group_rss_samples']<1:raise ValueError('terminal status')
if (p/'observations/attempt03/result.json').read_bytes()!=(o/'result.json').read_bytes() or (p/'observations/attempt03/compile.log').read_bytes()!=(o/'compile.log').read_bytes():raise ValueError('terminal copies')
for path,v in audit['guards_after'].items():
 x=Path(path)
 if v is None:
  if os.path.lexists(x):raise ValueError(('unexpected companion',path))
 elif not x.is_file() or str(x.resolve())!=v['realpath'] or sha(x)!=v['sha256']:raise ValueError(('guard',path))
expected="\n".join(["'DiophantineConsistency.RationalCarrier64.values_equal' depends on axioms: [propext, Quot.sound]","'DiophantineConsistency.RationalCarrier64.zero_iff' depends on axioms: [propext, Quot.sound]","'DiophantineConsistency.RationalCarrier64.value65_eq_carrier' depends on axioms: [propext]"])
if (p/'observations/attempt03/compile.log').read_text().strip()!=expected:raise ValueError('axioms')
print(json.dumps({'status':'PASS_LITERAL_ROW_AND_ARTIFACT_AUDIT','rows':[len(a),len(b)],'segments':[i,e-i+1,f-j+1,len(a)-e-1],'direct_guards':len(audit['guards_after']),'recorded_lean_exit':audit['exit'],'scope':'External literal transcription comparison plus Lean artifact recheck; no replay, fixed-leaf proof or transitive provider ancestry.'},sort_keys=True,indent=2))
