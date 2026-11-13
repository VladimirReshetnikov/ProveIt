#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';RDIR=BASE/'research/ordinary12-ipra-bridge';PKG=RDIR/'compact44-graph-derived-radix-prototype';PLAN=RDIR/'compact44-graph-derived-radix-closure-plan';OUT=Path('/tmp/ipra-compact-graph-derived-radix-pair-01');PREFIX=Path('/tmp/ipra-compact-fixed-graph-digits-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');PARENT=BASE/'reviews/compact44-fixed-graph-independent-audit';PLAN_AUDIT=BASE/'reviews/compact44-graph-radix-closure-independent-audit'
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 commit,receipt_hash='5248212201','799f5a7ce3fc8123acb1403eb241122446e7d4ed7ae5f327c65f44d722e11e48';prefix=PKG.relative_to(ROOT).as_posix()+'/evidence/'
 files=subprocess.run(['git','ls-tree','-r','--name-only',commit,'--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines();need(len([x for x in files if x.endswith('.log')])==6,'6 retained logs')
 for name in files:
  blob=subprocess.run(['git','show',commit+':'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(hashlib.sha256(blob).hexdigest()==sha(ROOT/name),'evidence drift '+name)
 need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==receipt_hash,'receipt')
 term=json.loads((PKG/'evidence/terminal-observation.json').read_bytes());need(term=={'session_id':20592,'observed_exit':0,'status':'PASS_PAIRED_COMPACT_GRAPH_DERIVED_RADIX','receipt_sha256':receipt_hash,'protected_head':'692b5249e6ec9c0c01b3bf080d03a22138526934'},'outer observation')
 need(sha(BASE/'reviews/compact44-graph-radix-prelaunch-independent-audit/CHECK.json')=='30b2a35f96f4fb320e6d0a4cdea94f04534dd25b901956c79220693aaefa3c2c','prelaunch audit receipt')
 rec=json.loads((OUT/'receipt.json').read_bytes());need(rec['status']=='PASS_PAIRED_COMPACT_GRAPH_DERIVED_RADIX' and len(rec['runs'])==2,'status')
 need(sha(PKG/'replay.py')==rec['driver_sha256'],'driver')
 for p,h in rec['fixed_inputs_sha256'].items():need(sha(p)==h,'fixed input '+p)
 need(sha(PLAN_AUDIT/'CHECK.json')=='43f29a866dd7c4b18acd6bc2dfe1de0a392ab4bd01d1554b778d4c700954bd84','closure audit receipt')
 parent=json.loads((PARENT/'CHECK.json').read_bytes());need(rec['graph_digit_audit']==parent and sha(PARENT/'CHECK.json')=='3d380723c818d4f16dc78e5c942b5e3cab8f7a01cf8a5bfad47ad3af3941abc1','parent receipt')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py'),parent['evidence_commit'],parent['receipt_sha256']],capture_output=True,timeout=1800);need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==parent,'parent audit rerun')
 scan=json.loads((PLAN/'scan.json').read_bytes());rows=scan['modules'];need(len(rows)==3 and len(scan['inherited_objects'])==140,'source closure counts');modules=[x['module'] for x in rows]
 guards=rec['direct_and_output_guards'];need(guards,'guards');expectedguards=set()
 for name,v in guards.items():
  p=Path(name)
  if v is None:need(not p.exists() and not p.is_symlink(),'unexpected companion '+name)
  else:need(p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],'guard '+name)
 result=[]
 for run,side in zip(rec['runs'],('author','peer')):
  need(run['label']==side and [x['module'] for x in run['steps']]==modules,'step order');lib=OUT/side/'lib';base=PREFIX/side/'lib';orig={p.relative_to(base) for p in base.rglob('*.olean')};actual={p.relative_to(lib) for p in lib.rglob('*.olean')};extra={Path(*n.split('.')).with_suffix('.olean') for n in modules};need(len(orig)==140 and not orig&extra and actual==orig|extra,'overlay inventory')
  for rel in orig:need((lib/rel).resolve()==(base/rel).resolve() and sha(lib/rel)==sha(base/rel),'overlay '+str(rel))
  available=set(orig);steps=[];total=0
  for ix,row in enumerate(run['steps']):
   name=row['module'];rel=Path(*name.split('.'));src=OUT/'frozen'/rel.with_suffix('.lean');obj=(lib/rel).with_suffix('.olean');log=OUT/side/(name.replace('.','_')+'.log');copy=PKG/'evidence'/side/log.name
   need(row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'child exits '+name)
   need(src.is_file() and not src.is_symlink() and sha(src)==row['source_sha256']==rows[ix]['source_sha256'] and obj.is_file() and not obj.is_symlink() and sha(obj)==row['object_sha256'] and sha(log)==sha(copy)==row['log_sha256'] and log.read_text()==row['stdout'],'artifacts '+name)
   cmd=row['command'];need(cmd[1:4]==['-M3000','-j1','-DElab.async=false'] and cmd[-3]==str(src) and cmd[-1]==str(obj),'command '+name)
   imports=[v for l in src.read_text().splitlines() if l.startswith('import ') for v in l[7:].split()];need(imports==rows[ix]['imports'],'imports '+name)
   init=PACKAGE/'Init.olean';need(init.is_file(),'required Init');deps={str(init)}
   for dep in imports:
    drel=Path(*dep.split('.')).with_suffix('.olean')
    if dep.startswith('DiophantineConsistency.'):need(drel in available,'same-side missing '+dep);candidate=lib/drel
    else:candidate=lib/drel if drel in available else PACKAGE/drel
    need(candidate.is_file(),'missing required object '+dep);deps.add(str(candidate))
   need(set(row['deps_stdout'].splitlines())==deps,'dependency paths '+name)
   for dep in deps|{str(obj)}:
    for suffix in SUFFIXES:expectedguards.add(dep[:-6]+suffix)
    entry=guards.get(dep);need(entry is not None and sha(dep)==entry['sha256'] and str(Path(dep).resolve())==entry['realpath'],'required direct/output guard '+dep)
   reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M);wanted=re.findall(r'^#print axioms\s+([^\s]+)',src.read_text(),re.M);need([n for n,_ in reports]==wanted and [[n,a] for n,a in reports]==row['axiom_reports'],'exact reports '+name)
   for n,ax in reports:need({x.strip() for x in ax.split(',')}=={'propext','Classical.choice','Quot.sound'},'axiom sets '+n)
   need(not re.search(r'warning:|error:|\bsorryAx\b|\bsorry\b',row['stdout']),'warning '+name)
   total+=len(reports);available.add(rel.with_suffix('.olean'));steps.append({'module':name,'source_sha256':row['source_sha256'],'object_sha256':row['object_sha256'],'log_sha256':row['log_sha256'],'recorded_compiler_exit':0,'recorded_deps_exit':0})
  client=(OUT/'frozen/DiophantineConsistency/CompactGraphDerivedRadix.lean').read_text()
  for token in ('theorem fixed_graph_digits (K : ℕ)','(hv : ∀ j,0<v j)','(hz : InternalZero','∃ N : V, 0<N','v 0=rep','dig 67 C 0=1','dig 67 C k≤3'):need(token in client,'fixed theorem scope '+token)
  need(total==4,'axiom report count');result.append({'side':side,'axiom_reports':total,'steps':steps})
 need(set(guards)==expectedguards,'complete direct/output guards');need(result[0]['steps']==result[1]['steps'],'paired outputs')
 print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT44_GRAPH_DERIVED_RADIX_AUDIT','evidence_commit':commit,'receipt_sha256':receipt_hash,'recorded_outer_session':20592,'recorded_outer_exit':0,'protected_head':term['protected_head'],'parent_audit_rerun_exit':q.returncode,'direct_and_output_guard_paths':len(guards),'runs':result,'scope':'IΣ₁ model graph-derived positive radix/repunit and digit bounds for symbolic beta/masks with arbitrary K, assuming positive variables and graph zero; retained graph/K binding, checker, machine and iPRA endpoint remain open.'},indent=2))
if __name__=='__main__':main()
