#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';RDIR=BASE/'research/ordinary12-ipra-bridge';PKG=RDIR/'compact44-fixed-graph-digits-prototype';PLAN=RDIR/'compact44-fixed-graph-closure-plan';OUT=Path('/tmp/ipra-compact-fixed-graph-digits-pair-01');PREFIX=Path('/tmp/ipra-compact-symbolic-graph-join-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');PARENT=BASE/'reviews/compact44-symbolic-graph-join-independent-audit';PLAN_AUDIT=BASE/'reviews/compact44-fixed-graph-closure-independent-audit'
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 commit,receipt_hash=sys.argv[1:];prefix=PKG.relative_to(ROOT).as_posix()+'/evidence/'
 files=subprocess.run(['git','ls-tree','-r','--name-only',commit,'--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines();need(len([x for x in files if x.endswith('.log')])==12,'12 retained logs')
 for name in files:
  blob=subprocess.run(['git','show',commit+':'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(hashlib.sha256(blob).hexdigest()==sha(ROOT/name),'evidence drift '+name)
 need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==receipt_hash,'receipt')
 term=json.loads((PKG/'evidence/terminal-observation.json').read_bytes());need(term=={'session_id':89018,'observed_exit':0,'status':'PASS_PAIRED_COMPACT_FIXED_GRAPH_DIGITS','receipt_sha256':receipt_hash,'protected_head':'b1619eb5c62f2820392cac7502429e3cc087c69b'},'outer observation')
 need(sha(BASE/'reviews/compact44-fixed-graph-prelaunch-audit/CHECK.json')=='ca82baad318a99889c675e3f8b19263a50af017daae7ec0bf8e7b7533d602121','prelaunch audit receipt')
 rec=json.loads((OUT/'receipt.json').read_bytes());need(rec['status']=='PASS_PAIRED_COMPACT_FIXED_GRAPH_DIGITS' and len(rec['runs'])==2,'status')
 need(sha(PKG/'replay.py')==rec['driver_sha256'],'driver')
 for p,h in rec['fixed_inputs_sha256'].items():need(sha(p)==h,'fixed input '+p)
 need(sha(PLAN_AUDIT/'CHECK.json')=='363986d2a3575920a4fcd069560aef98b1a8ad0eb23fa46af58f0fc222e8af9f','closure audit receipt')
 parent=json.loads((PARENT/'CHECK.json').read_bytes());need(rec['graph_digit_audit']==parent and sha(PARENT/'CHECK.json')=='3164ef421742c093b07fb1ff491c19d9586f2ff19f83d2371f3311b4958721ec','parent receipt')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py'),parent['evidence_commit'],parent['receipt_sha256']],capture_output=True,timeout=1800);need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==parent,'parent audit rerun')
 scan=json.loads((PLAN/'scan.json').read_bytes());rows=scan['modules'];need(len(rows)==6 and len(scan['inherited_objects'])==134,'source closure counts');modules=[x['module'] for x in rows]
 guards=rec['direct_and_output_guards'];need(guards,'guards');expectedguards=set()
 for name,v in guards.items():
  p=Path(name)
  if v is None:need(not p.exists() and not p.is_symlink(),'unexpected companion '+name)
  else:need(p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],'guard '+name)
 result=[]
 for run,side in zip(rec['runs'],('author','peer')):
  need(run['label']==side and [x['module'] for x in run['steps']]==modules,'step order');lib=OUT/side/'lib';base=PREFIX/side/'lib';orig={p.relative_to(base) for p in base.rglob('*.olean')};actual={p.relative_to(lib) for p in lib.rglob('*.olean')};extra={Path(*n.split('.')).with_suffix('.olean') for n in modules};need(len(orig)==134 and not orig&extra and actual==orig|extra,'overlay inventory')
  for rel in orig:need((lib/rel).resolve()==(base/rel).resolve() and sha(lib/rel)==sha(base/rel),'overlay '+str(rel))
  available=set(orig);steps=[];total=0
  for ix,row in enumerate(run['steps']):
   name=row['module'];rel=Path(*name.split('.'));src=OUT/'frozen'/rel.with_suffix('.lean');obj=(lib/rel).with_suffix('.olean');log=OUT/side/(name.replace('.','_')+'.log');copy=PKG/'evidence'/side/log.name
   need(row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'child exits '+name)
   need(sha(src)==row['source_sha256']==rows[ix]['source_sha256'] and obj.is_file() and not obj.is_symlink() and sha(obj)==row['object_sha256'] and sha(log)==sha(copy)==row['log_sha256'] and log.read_text()==row['stdout'],'artifacts '+name)
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
  need(total==10,'axiom report count');result.append({'side':side,'axiom_reports':total,'steps':steps})
 need(set(guards)==expectedguards,'complete direct/output guards');need(result[0]['steps']==result[1]['steps'],'paired outputs')
 print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT44_FIXED_GRAPH_DIGITS_AUDIT','evidence_commit':commit,'receipt_sha256':receipt_hash,'recorded_outer_session':89018,'recorded_outer_exit':0,'protected_head':term['protected_head'],'parent_audit_rerun_exit':q.returncode,'direct_and_output_guard_paths':len(guards),'runs':result,'scope':'IΣ₁ model symbolic fixed-port graph digit theorem with arbitrary K, explicit positive graph zero, positive witnesses, radix and repunit assumptions; external retained graph/K binding, checker, machine and iPRA endpoint remain open.'},indent=2))
if __name__=='__main__':main()
