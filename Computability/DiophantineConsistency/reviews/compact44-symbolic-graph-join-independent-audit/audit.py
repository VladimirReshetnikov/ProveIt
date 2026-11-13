#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';RDIR=BASE/'research/ordinary12-ipra-bridge';PKG=RDIR/'compact44-symbolic-graph-join-prototype';PLAN=RDIR/'compact44-symbolic-graph-closure-plan';OUT=Path('/tmp/ipra-compact-symbolic-graph-join-pair-01');PREFIX=Path('/tmp/ipra-freej-concrete-digits-client-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');PRE=BASE/'reviews/compact44-symbolic-graph-join-prelaunch-audit';GRAPH=BASE/'reviews/ordinary12-freej-concrete-digits-client-independent-audit';LOW=BASE/'reviews/compact44-low-even-independent-audit'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 commit,receipt_hash=sys.argv[1:];prefix=PKG.relative_to(ROOT).as_posix()+'/evidence/'
 files=subprocess.run(['git','ls-tree','-r','--name-only',commit,'--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines();need(len([x for x in files if x.endswith('.log')])==14,'14 retained logs')
 for name in files:
  blob=subprocess.run(['git','show',commit+':'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(hashlib.sha256(blob).hexdigest()==sha(ROOT/name),'retained evidence drift '+name)
 need(sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==receipt_hash,'receipt')
 term=json.loads((PKG/'evidence/terminal-observation.json').read_bytes());need(term=={'session_id':36951,'observed_exit':0,'status':'PASS_PAIRED_COMPACT_SYMBOLIC_GRAPH_JOIN','receipt_sha256':receipt_hash,'protected_head':'4634912ff5281950cf4517ed0146062a06dff813'},'outer terminal observation')
 rec=json.loads((OUT/'receipt.json').read_bytes());need(rec['status']=='PASS_PAIRED_COMPACT_SYMBOLIC_GRAPH_JOIN' and len(rec['runs'])==2,'status')
 need(sha(PKG/'replay.py')==rec['driver_sha256']=='71c0e0da4a04e62152a37ac68fd940487d14df2f0ed47cacfdbc35506e7934ad','driver')
 for p,h in rec['fixed_inputs_sha256'].items():need(sha(p)==h,'fixed input '+p)
 need(sha(PRE/'CHECK.json')=='639eebb031fa2868fa0464b131f97213a1776dbbe85c2fb1fd9ced44a1b1e55d','prelaunch receipt')
 for directory,key in ((GRAPH,'graph_digit_audit'),(LOW,'low_even_audit')):
  q=subprocess.run([sys.executable,'-I','-S','-B',str(directory/'audit.py')],capture_output=True,timeout=1200);need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((directory/'CHECK.json').read_bytes())==rec[key],'parent audit '+str(directory))
 scan=json.loads((PLAN/'scan.json').read_bytes());rows=scan['modules'];need(len(rows)==7,'source count');modules=[x['module'] for x in rows]
 result=[]
 for run,side in zip(rec['runs'],('author','peer')):
  need(run['label']==side and [x['module'] for x in run['steps']]==modules,'step order');lib=OUT/side/'lib';base=PREFIX/side/'lib';orig={p.relative_to(base) for p in base.rglob('*.olean')};actual={p.relative_to(lib) for p in lib.rglob('*.olean')};extra={Path(*n.split('.')).with_suffix('.olean') for n in modules};need(len(orig)==127 and not orig&extra and actual==orig|extra,'overlay inventory')
  for rel in orig:need((lib/rel).resolve()==(base/rel).resolve() and sha(lib/rel)==sha(base/rel),'overlay '+str(rel))
  available=set(orig);steps=[];total=0
  for ix,row in enumerate(run['steps']):
   name=row['module'];rel=Path(*name.split('.'));src=OUT/'frozen'/rel.with_suffix('.lean');obj=(lib/rel).with_suffix('.olean');log=OUT/side/(name.replace('.','_')+'.log');copy=PKG/'evidence'/side/log.name
   need(row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'child exits '+name)
   need(sha(src)==row['source_sha256']==rows[ix]['source_sha256'] and obj.is_file() and not obj.is_symlink() and sha(obj)==row['object_sha256'] and sha(log)==sha(copy)==row['log_sha256'] and log.read_text()==row['stdout'],'artifacts '+name)
   cmd=row['command'];need(cmd[1:4]==['-M3000','-j1','-DElab.async=false'] and cmd[-3]==str(src) and cmd[-1]==str(obj),'command '+name)
   imports=[v for l in src.read_text().splitlines() if l.startswith('import ') for v in l[7:].split()];need(imports==rows[ix]['imports'],'imports '+name)
   init=PACKAGE/'Init.olean';need(init.is_file(),'required Init exists');deps={str(init)}
   for dep in imports:
    drel=Path(*dep.split('.')).with_suffix('.olean')
    if dep.startswith('DiophantineConsistency.'):need(drel in available,'same-side missing '+dep);candidate=lib/drel
    else:candidate=lib/drel if drel in available else PACKAGE/drel
    need(candidate.is_file(),'missing required object '+dep);deps.add(str(candidate))
   need(set(row['deps_stdout'].splitlines())==deps,'dependency paths '+name)
   reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M);wanted=re.findall(r'^#print axioms\s+([^\s]+)',src.read_text(),re.M);need([n for n,_ in reports]==wanted and [[n,a] for n,a in reports]==row['axiom_reports'],'exact report names '+name)
   for n,ax in reports:need({x.strip() for x in ax.split(',')}==({'propext'} if n=='CompactHighResidue.natural_mod_eight' else {'propext','Classical.choice','Quot.sound'}),'axiom sets '+n)
   need(not re.search(r'warning:|error:|\bsorryAx\b|\bsorry\b',row['stdout']),'warning '+name)
   total+=len(reports);available.add(rel.with_suffix('.olean'));steps.append({'module':name,'source_sha256':row['source_sha256'],'object_sha256':row['object_sha256'],'log_sha256':row['log_sha256'],'recorded_compiler_exit':0,'recorded_deps_exit':0})
  need(total==10,'axiom report count');result.append({'side':side,'axiom_reports':total,'steps':steps})
 need(result[0]['steps']==result[1]['steps'],'paired outputs')
 print(json.dumps({'status':'PASS_INDEPENDENT_SYMBOLIC_GRAPH_JOIN_PAIR_AUDIT','evidence_commit':commit,'receipt_sha256':receipt_hash,'recorded_outer_session':36951,'recorded_outer_exit':0,'protected_head':term['protected_head'],'parent_audit_reruns_exit':0,'runs':result,'scope':'IΣ₁ conditional graph digit theorem with explicit low/high symbolic port equalities and graph, positivity, radix, split and product assumptions; no retained-port calibration, checker, machine or iPRA endpoint. Inherited provider/dynamic and sampled resource limitations.'},indent=2))
if __name__=='__main__':main()
