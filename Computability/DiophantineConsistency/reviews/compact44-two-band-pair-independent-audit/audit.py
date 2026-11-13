#!/usr/bin/env python3
"""Independent read-only retained two-band rotation pair artifact check."""
import hashlib,json,os,re,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site: raise RuntimeError('requires python3 -I -S -B')
ROOT=Path.cwd()/'Computability/DiophantineConsistency'; BASE=ROOT/'research/ordinary12-ipra-bridge'; P=BASE/'compact44-two-band-rotation-pair-prototype'; E=P/'evidence'; PLAN=BASE/'compact44-two-band-rotation-closure-plan'; PA=ROOT/'reviews/compact44-coefficient-decomposition-independent-audit'; CA=ROOT/'reviews/compact44-two-band-rotation-closure-independent-audit'; OUT=Path('/tmp/ipra-two-band-rotation-pair-01'); PARENT=Path('/tmp/ipra-compact-coefficient-decomposition-pair-01'); PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'); HERE=Path(__file__).resolve().parent
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def h(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
receipt_hash='481dd5da98efb12d3347490c0e73fd60f64e2767bc3e6aa27b0bb1d3af5d81ca'; driver_hash='24c5b85c8f1b19b0b40dd4304eadb42a2c5365b147f1238a372dca0b0397a777'; parent_hash='2351c55148f2e3eb4b8ac51894050dbfd942eef7fdad26030251cbf637e94432'; closure_hash='31cac5d8ced31e78f45194b9dfa2edd0e2e1005ed26396187a400ac85ed242ba'
need(h(E/'receipt.json')==receipt_hash and (E/'receipt.json').read_bytes()==(OUT/'receipt.json').read_bytes(),'receipt drift');r=json.loads((E/'receipt.json').read_bytes());terminal=json.loads((E/'terminal-observation.json').read_bytes())
need(r['status']=='PASS_PAIRED_TWO_BAND_ROTATION' and r['driver_sha256']==driver_hash and h(P/'replay.py')==driver_hash and r['protected_head']=='bc5bf1e4e571e6d6af1588b455e68760a63dc6d5','receipt schema')
need(type(terminal['observed_exit']) is int and terminal['observed_exit']==0 and terminal['session_id']==47256 and terminal['receipt_sha256']==receipt_hash and terminal['protected_head']==r['protected_head'],'terminal')
need(terminal['lean_processes_remaining'] is False and terminal['source_path']==str(OUT) and h(E/'progress.json')==terminal['progress_sha256'] and (E/'progress.json').read_bytes()==(OUT/'progress.json').read_bytes(),'terminal progress')
need(h(PA/'CHECK.json')==parent_hash and h(CA/'CHECK.json')==closure_hash,'parent hash');parent=json.loads((PA/'CHECK.json').read_bytes());closure=json.loads((CA/'CHECK.json').read_bytes());need(r['parent_audit']==parent,'parent receipt mismatch')
for audit,expected in [('parent',parent),('closure',closure)]:
 need(json.loads((HERE/'observations'/f'{audit}-rerun.stdout').read_bytes())==expected and not (HERE/'observations'/f'{audit}-rerun.stderr').read_bytes(),('audit rerun mismatch',audit))
for p,digest in r['fixed_pins'].items():need(Path(p).is_file() and h(p)==digest,('fixed pin',p))
nested=json.loads((HERE/'observations/nested-rerun.stdout').read_bytes()); grandparents=[ROOT/'reviews/compact44-943-decoder-independent-audit/CHECK.json',ROOT/'reviews/compact44-coefficient-mass-independent-audit/CHECK.json']; need(nested=={'scan':json.loads((BASE/'compact44-coefficient-decomposition-closure-plan/scan.json').read_bytes()),'parent':[json.loads(x.read_bytes()) for x in grandparents]} and not (HERE/'observations/nested-rerun.stderr').read_bytes(),'nested parent rerun mismatch')
scan=json.loads((PLAN/'scan.json').read_bytes());need((HERE/'observations/scan-rerun.stdout').read_bytes()==(PLAN/'scan.json').read_bytes() and not (HERE/'observations/scan-rerun.stderr').read_bytes(),'scan rerun');sources=scan['source_order'];need(len(sources)==3,'source count')
modules=['DiophantineConsistency.'+x for x in ['CompactPartialBand','CompactPartialBandRotation','TwoBand']];need([x['module'] for x in sources]==modules,'source order')
need(len(r['runs'])==2 and [x['side'] for x in r['runs']]==['author','peer'],'sides');summaries=[];stems={PACKAGE/'Init'};expected_new={Path(*n.split('.')).with_suffix('.olean') for n in modules}
for side,run in zip(('author','peer'),r['runs']):
 lib=OUT/side/'lib';old=PARENT/side/'lib';aa={p.relative_to(old):p for p in old.rglob('*.olean')};bb={p.relative_to(lib):p for p in lib.rglob('*.olean')};need(len(aa)==126 and set(bb)==set(aa)|expected_new and len(bb)==129,('provider inventory',side,len(aa),len(bb)))
 for rel in aa:need(h(aa[rel])==h(bb[rel]) and aa[rel].resolve()==bb[rel].resolve(),('inherited object mismatch',side,str(rel)))
 need(len(run['steps'])==3,('step count',side))
 for row,src in zip(run['steps'],sources):
  name=src['module'];need(row['module']==name and type(row['compiler_exit']) is int and row['compiler_exit']==0 and type(row['deps_exit']) is int and row['deps_exit']==0 and row['stop_reason'] is None,('step status',side,name))
  frozen=(OUT/'frozen'/Path(*name.split('.'))).with_suffix('.lean');obj=(lib/Path(*name.split('.'))).with_suffix('.olean');log=OUT/side/(name.replace('.','_')+'.log');saved=E/side/log.name
  need(frozen.is_file() and not frozen.is_symlink() and h(frozen)==src['sha256']==row['source_sha256'] and h(src['source'])==row['source_sha256'],('source',side,name))
  need([line[7:] for line in frozen.read_text().splitlines() if line.startswith('import ')]==src['imports'],('imports',side,name))
  need(obj.is_file() and not obj.is_symlink() and h(obj)==row['object_sha256'],('object',side,name));need(log.is_file() and saved.read_bytes()==log.read_bytes() and h(log)==row['log_sha256'] and log.read_text()==row['stdout'],('log',side,name))
  text=row['stdout'];need(re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text) is None,('diagnostics',side,name));reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",text,re.M);need(len(reports)==len(src['reports']) and {x for x,_ in reports}==set(src['reports']) and all({x.strip() for x in ax.split(',') if x.strip()}=={'propext','Classical.choice','Quot.sound'} for n,ax in reports) and [list(x) for x in reports]==row['axiom_reports'],('axioms',side,name))
  expected={str(PACKAGE/'Init.olean')}|{str((lib/Path(*dep.split('.'))).with_suffix('.olean')) for dep in src['imports']};lines=row['deps_stdout'].splitlines();need(set(lines)==expected and 1<=lines.count(str(PACKAGE/'Init.olean'))<=2 and all(lines.count(x)==1 for x in expected if x!=str(PACKAGE/'Init.olean')),('dependencies',side,name))
  lean='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean';need(row['command']==[lean,'-M3000','-j1','-DElab.async=false','--root='+str(OUT/'frozen'),str(frozen),'-o',str(obj)],('command',side,name))
  stems.add(Path(str(obj)[:-6]));stems.update(Path(x[:-6]) for x in expected);summaries.append({'side':side,'module':name,'object_sha256':h(obj),'axiom_names':sorted(n for n,_ in reports),'sampled_peak_rss_bytes':row['sampled_peak_rss_bytes']})
need(len(stems)==11 and set(r['guards'])=={str(stem)+suffix for stem in stems for suffix in SUFFIXES} and len(r['guards'])==110,'guard slot set')
for name,prior in r['guards'].items():
 p=Path(name)
 if prior is None:need(not os.path.lexists(p),('unexpected companion',name))
 else:need(p.is_file() and str(p.resolve())==prior['realpath'] and h(p)==prior['sha256'],('guard drift',name))
for left,right in zip(r['runs'][0]['steps'],r['runs'][1]['steps']):need(left['object_sha256']==right['object_sha256'] and left['stdout']==right['stdout'] and left['axiom_reports']==right['axiom_reports'],'paired mismatch')
print(json.dumps({'status':'PASS_INDEPENDENT_TWO_BAND_ROTATION_PAIR_ARTIFACT_AUDIT','receipt_sha256':receipt_hash,'recorded_outer_session':47256,'recorded_outer_exit':0,'source_modules':3,'runs':summaries,'inherited_objects_per_side':126,'guard_slots':110,'lean_launched':False,'scope':'Conditional IΣ₁-model two-band and five-monomial congruence under explicit hK, positive period/modulus and graph congruence; w*C remains a separate residual. No retained-byte binding, fractional rotation, full weighted column, decoder, machine or internal iPRA theorem.'},indent=2,sort_keys=True))
