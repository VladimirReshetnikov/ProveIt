#!/usr/bin/env python3
"""Independent read-only verification of retained selector graph pair."""
import hashlib,json,os,re,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('invoke with python3 -I -S -B without optimization')
ROOT=Path.cwd()/'Computability/DiophantineConsistency';BASE=ROOT/'research/ordinary12-ipra-bridge';P=BASE/'compact44-selector-graph-pair-prototype';E=P/'evidence';PLAN=BASE/'compact44-selector-graph-closure-plan';PARENT_AUDIT=ROOT/'reviews/compact44-same-witness-saturation-independent-audit';OUT=Path('/tmp/ipra-selector-graph-pair-01');PARENT=Path('/tmp/ipra-same-witness-saturation-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');HERE=Path(__file__).resolve().parent
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
receipt_hash='3478cdb0597c6b2e86df02f58e3210c932b954e591338382a7cb4f6b06495a16';driver_hash='f6a4b8321fa2c532d55c6816d5fbd7c9ebe981604949c1695340f965f3525117';parent_hash='5d8c620fc76d741a7d1b398f9e442ce7dfea83a90cd39a42c53e9320d75dd754'
need(h(E/'receipt.json')==receipt_hash and (E/'receipt.json').read_bytes()==(OUT/'receipt.json').read_bytes(),'receipt drift');r=json.loads((E/'receipt.json').read_bytes());terminal=json.loads((E/'terminal-observation.json').read_bytes())
need(r['status']=='PASS_PAIRED_SELECTOR_GRAPH' and r['driver_sha256']==driver_hash and h(P/'replay.py')==driver_hash and r['protected_head']=='438e874a18e5e21189fa5160b8b6448a1304a492','pair receipt schema')
need(type(terminal['observed_exit']) is int and terminal['observed_exit']==0 and terminal['session_id']==72622 and terminal['receipt_sha256']==receipt_hash and terminal['protected_head']==r['protected_head'],'outer terminal observation')
need(h(PARENT_AUDIT/'CHECK.json')==parent_hash,'parent receipt drift');parent=json.loads((PARENT_AUDIT/'CHECK.json').read_bytes());need(r['parent_audit']==parent,'parent receipt mismatch')
parent_observed=json.loads((HERE/'observations/parent-rerun.stdout').read_bytes());need(parent_observed==parent and not (HERE/'observations/parent-rerun.stderr').read_bytes(),'parent rerun mismatch')
for p,digest in r['fixed_pins'].items():need(Path(p).is_file() and h(p)==digest,('fixed input drift',p))
scan=json.loads((PLAN/'scan.json').read_bytes());sources=scan['source_order'];need(len(sources)==4,'source count')
modules=['DiophantineConsistency.CompactPositionIncrement','DiophantineConsistency.CompactPositionGraph','DiophantineConsistency.CompactSelectorMask','DiophantineConsistency.CompactSelectorGraph'];names=[{'CompactPositionCarry.increment_digits'},{'CompactPositionCarry.generic_position_noCarry','CompactPositionCarry.fixed_position_noCarry'},{'CompactSelectorMask.selector_mask_digit','CompactSelectorMask.absent_mask_digit'},{'CompactSelectorGraph.selector_slot','CompactSelectorGraph.excluded_slot','CompactSelectorGraph.fixed_graph_selector_bounds'}];need([x['module'] for x in sources]==modules,'source order')
need(len(r['runs'])==2 and [x['side'] for x in r['runs']]==['author','peer'],'sides');summaries=[];stems={PACKAGE/'Init'};expected_new={Path(*n.split('.')).with_suffix('.olean') for n in modules}
for side,run in zip(('author','peer'),r['runs']):
 lib=OUT/side/'lib';old=PARENT/side/'lib';aa={p.relative_to(old):p for p in old.rglob('*.olean')};bb={p.relative_to(lib):p for p in lib.rglob('*.olean')};need(len(aa)==146 and set(bb)==set(aa)|expected_new and len(bb)==150,('provider inventory',side))
 for rel in aa:need(h(aa[rel])==h(bb[rel]),('inherited object mismatch',side,str(rel)))
 need(len(run['steps'])==4,('step count',side))
 for row,src,nm in zip(run['steps'],sources,names):
  name=src['module'];need(row['module']==name and type(row['compiler_exit']) is int and row['compiler_exit']==0 and type(row['deps_exit']) is int and row['deps_exit']==0 and row['stop_reason'] is None,('step status',side,name))
  frozen=(OUT/'frozen'/Path(*name.split('.'))).with_suffix('.lean');obj=(lib/Path(*name.split('.'))).with_suffix('.olean');log=OUT/side/(name.replace('.','_')+'.log');saved=E/side/log.name
  need(frozen.is_file() and not frozen.is_symlink() and h(frozen)==src['source_sha256']==row['source_sha256'] and h(src['source'])==row['source_sha256'],('source',side,name))
  need(obj.is_file() and not obj.is_symlink() and h(obj)==row['object_sha256'],('object',side,name));need(log.is_file() and saved.read_bytes()==log.read_bytes() and h(log)==row['log_sha256'] and log.read_text()==row['stdout'],('log',side,name))
  text=row['stdout'];need(re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text) is None,('diagnostics',side,name));reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",text,re.M);need(len(reports)==len(nm) and {x for x,_ in reports}==nm and all({x.strip() for x in ax.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,ax in reports) and [list(x) for x in reports]==row['axiom_reports'],('axioms',side,name))
  expected={str(PACKAGE/'Init.olean')}|{str((lib/Path(*dep.split('.'))).with_suffix('.olean')) for dep in src['imports']};lines=row['deps_stdout'].splitlines();need(set(lines)==expected and 1<=lines.count(str(PACKAGE/'Init.olean'))<=2 and all(lines.count(x)==1 for x in expected if x!=str(PACKAGE/'Init.olean')),('dependencies',side,name))
  lean='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean';need(row['command']==[lean,'-M3000','-j1','-DElab.async=false','--root='+str(OUT/'frozen'),str(frozen),'-o',str(obj)],('command',side,name))
  stems.add(Path(str(obj)[:-6]));stems.update(Path(x[:-6]) for x in expected);summaries.append({'side':side,'module':name,'object_sha256':h(obj),'axiom_names':sorted(n for n,_ in reports),'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
need(len(stems)==13 and set(r['guards'])=={str(stem)+suffix for stem in stems for suffix in SUFFIXES} and len(r['guards'])==130,'guard slot set')
for name,old in r['guards'].items():
 p=Path(name)
 if old is None:need(not os.path.lexists(p),('unexpected companion',name))
 else:need(p.is_file() and str(p.resolve())==old['realpath'] and h(p)==old['sha256'],('guard drift',name))
for left,right in zip(r['runs'][0]['steps'],r['runs'][1]['steps']):need(left['object_sha256']==right['object_sha256'] and left['stdout']==right['stdout'],'paired mismatch')
print(json.dumps({'status':'PASS_INDEPENDENT_SELECTOR_GRAPH_PAIR_ARTIFACT_AUDIT','receipt_sha256':receipt_hash,'recorded_outer_session':72622,'recorded_outer_exit':0,'source_modules':4,'runs':summaries,'inherited_objects_per_side':146,'guard_slots':130,'lean_launched':False,'scope':'Common N,w under positive graph coordinates and literal zero at fixed symbolic beta/masks with arbitrary K. Selector digit bounds retain k>0, k<8807*N and residue hypotheses; index 1 is zero. No retained-byte, weighted graph-column, decoder, machine or internal iPRA theorem.'},indent=2,sort_keys=True))
