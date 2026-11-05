#!/usr/bin/env python3
"""Read-only literal-row transcription and retained Lean artifact review."""
import hashlib,json,os,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2]; p=r/'research/rational-carrier64-current14-base-draft';q=r/'research/rational-carrier64-independent';o=Path('/tmp/rational-carrier64-current14-base-priority-check04')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
pins={p/'RationalCarrier64Current.lean':'beb7b4e898dddb4f0c8bbf1fcccd24b7d57e56df5b48e53c76754c6d51776ec1',p/'build_source.py':'cd3635869afb4f7e1044d873614246077ca77888afdef69777e477a388cbe52c',q/'polynomial.json':'8fd205a43c4045914d88f4117ba263cf7a232ac26c64dcf09a1c37a8d88e7b27',q/'source/parent65.json':'408dde55352b837db3c606db446f3bf41dc7fd6d9242808ba4a123930bf0b5ff',p/'check04.py':'2a1d59751f35d7bdcaacab8760adabc7d3ef295a0db2b3d304f2d86fcc8b30b0',p/'observations/attempt04/result.json':'1aa7f92b832669e21aebae740f5df7ffad372d0ccd76ca7a196d2f58ae0d1ca0',p/'observations/attempt04/compile.log':'5088fa4b24c72b2d1ecf81861e65f33ef0d1b60c92bd0bc194a71fc521b0511d',o/'RationalCarrier64Current.olean':'ac3ccf83d8c6c49be8f7b9d306311f2d6fe42f317a4d7fc9b5f875890526b34b',Path('/tmp/current14-standard-fresh-build-20261104/lib/DiophantineConsistency/CurrentEquationSyntax2011.olean'):'28e2a026978eb60c2fb0ef494b1c7256a1b1aa354ac4ee9f3688a9433d48daae',Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Mathlib/Tactic/Ring.olean'):'cc12dfa66db7ef6ae4cd2d7a4e035ddffaca827168243f728812776b77836eb4'}
for f,h in pins.items():
 if not f.is_file() or sha(f)!=h:raise ValueError(('pin',str(f)))
d64=json.loads((q/'polynomial.json').read_bytes());d65=json.loads((q/'source/parent65.json').read_bytes());a=d64['source'];b=d65['source']
if len(a)!=64 or len(b)!=65 or d64['witnesses']!=d65['witnesses']:raise ValueError('graph inventory')
i=next(i for i,row in enumerate(a) if row[0]=='q2minus1'); j=next(i for i,row in enumerate(b) if row[0]=='q2minus1');e=next(i for i,row in enumerate(a) if row[0]=='R');f=next(i for i,row in enumerate(b) if row[0]=='R')
if a[:i]!=b[:j] or a[e+1:]!=b[f+1:]:raise ValueError('shared rows')
s=(p/'RationalCarrier64Current.lean').read_text()
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
previous=(r/'research/rational-carrier64-lean-identity/RationalCarrier64.lean').read_text()
if s.split('structure Head ',1)[1].split('/-- Bind the literal 65-row graph',1)[0]!=previous.split('structure Head ',1)[1].split('/-- Binding to the existing 65-operation',1)[0]:raise ValueError('previous literal body drift')
manifest_path=Path('/tmp/current14-standard-fresh-source-20261104/manifest.json'); state_path=Path('/tmp/current14-standard-fresh-build-20261104/state.json'); snapshot=Path('/tmp/current14-standard-fresh-source-20261104/src/DiophantineConsistency/CurrentEquationSyntax2011.lean')
if sha(manifest_path)!='1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749' or sha(state_path)!='f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014':raise ValueError('base pins')
m=json.loads(manifest_path.read_bytes()); state=json.loads(state_path.read_bytes()); mod='DiophantineConsistency.CurrentEquationSyntax2011'; rec=next(x for x in state['records'] if x['module']==mod)
if state['status']!='PASS' or state['source_status']!='CURRENT_AT_FINAL_CHECK' or rec['exit']!=0 or rec['source_sha256']!=sha(snapshot) or rec['source_sha256']!=m['sources'][mod]['sha256'] or rec['object_sha256']!='28e2a026978eb60c2fb0ef494b1c7256a1b1aa354ac4ee9f3688a9433d48daae':raise ValueError('base provenance')
if state['manifest_sha256']!=sha(manifest_path) or set(rec['direct_inputs'])-{'Init'}!=set(m['sources'][mod]['imports']):raise ValueError('base manifest link or direct imports')
if sha(Path(rec['log']))!=rec['log_sha256']:raise ValueError('base producer log drift')
workspace=r/'Lean/DiophantineConsistency/CurrentEquationSyntax2011.lean'
if sha(workspace)!=sha(snapshot):raise ValueError('workspace source drift')
for item in rec['direct_inputs'].values():
 if sha(Path(item['path']))!=item['sha256']:raise ValueError('base direct input drift')
audit=json.loads((p/'observations/attempt04/result.json').read_bytes())
if audit['status']!='PASS' or audit['exit']!=0 or audit['stop_reason'] is not None or not audit['guards_stable'] or audit['guards_before']!=audit['guards_after'] or audit['group_rss_samples']<1:raise ValueError('terminal status')
if (p/'observations/attempt04/result.json').read_bytes()!=(o/'result.json').read_bytes() or (p/'observations/attempt04/compile.log').read_bytes()!=(o/'compile.log').read_bytes():raise ValueError('terminal copies')
for path,v in audit['guards_after'].items():
 x=Path(path)
 if v is None:
  if os.path.lexists(x):raise ValueError(('unexpected companion',path))
 elif not x.is_file() or str(x.resolve())!=v['realpath'] or sha(x)!=v['sha256']:raise ValueError(('guard',path))
expected="\n".join(["'DiophantineConsistency.RationalCarrier64Current.values_equal' depends on axioms: [propext, Quot.sound]","'DiophantineConsistency.RationalCarrier64Current.zero_iff' depends on axioms: [propext, Quot.sound]","'DiophantineConsistency.RationalCarrier64Current.value65_eq_expressionAt' depends on axioms: [propext]"])
if (p/'observations/attempt04/compile.log').read_text().strip()!=expected:raise ValueError('axioms')
print(json.dumps({'status':'PASS_LITERAL_ROW_AND_ARTIFACT_AUDIT','rows':[len(a),len(b)],'segments':[i,e-i+1,f-j+1,len(a)-e-1],'direct_guards':len(audit['guards_after']),'recorded_lean_exit':audit['exit'],'scope':'External literal transcription comparison and base direct provenance recheck; no Lean replay, fixed-leaf proof or transitive provider ancestry.'},sort_keys=True,indent=2))
