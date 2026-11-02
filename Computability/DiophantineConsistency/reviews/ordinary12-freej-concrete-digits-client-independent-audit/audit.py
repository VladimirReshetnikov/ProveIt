#!/usr/bin/env python3
"""Read-only audit of 26 conditional graph-to-symbolic-digit build artifacts."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';RESEARCH=BASE/'research/ordinary12-ipra-bridge';PKG=RESEARCH/'free-j-concrete-digits-client-prototype'
OUT=Path('/tmp/ipra-freej-concrete-digits-client-pair-01');PREFIX=Path('/tmp/ipra-freej-saturation-client-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PLAN=RESEARCH/'free-j-concrete-digits-closure-plan';PARENT=BASE/'reviews/ordinary12-freej-saturation-client-independent-audit';PLAN_AUDIT=BASE/'reviews/ordinary12-freej-concrete-digits-closure-independent-audit';PRE=BASE/'reviews/ordinary12-freej-concrete-digits-client-prelaunch-audit'
R='be3cb000febaa492605757160c1f00e8ffdc8be28457c55764dab15425a65689';DRIVER='9b760773ff4a03a67226406868ecc3de17902154c9515da20e502024f408a6bf'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
def main():
 prefix=PKG.relative_to(ROOT).as_posix()+'/'
 names=subprocess.run(['git','ls-tree','-r','--name-only','04f0521ce9','--',prefix],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines();need(len([x for x in names if '/evidence/' in x and x.endswith('.log')])==26,'tracked logs')
 for name in names:
  blob=subprocess.run(['git','show','04f0521ce9:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout;need(hashlib.sha256(blob).hexdigest()==sha(ROOT/name),'packet drift '+name)
 need(sha(PKG/'replay.py')==DRIVER and sha(PKG/'evidence/receipt.json')==sha(OUT/'receipt.json')==R,'driver/receipt')
 term=(PKG/'evidence/terminal.txt').read_text();need('session 32593 exit 0' in term and '23bd9093c8f39484082859c59737e6406dca2552' in term and term.rstrip().endswith('PASS_PAIRED_FREEJ_CONCRETE_DIGITS_CLIENT '+R),'outer observation')
 rec=json.loads((PKG/'evidence/receipt.json').read_bytes());need(rec['status']=='PASS_PAIRED_FREEJ_CONCRETE_DIGITS_CLIENT' and len(rec['runs'])==2,'receipt status')
 for p,h in rec['fixed_inputs_sha256'].items():need(sha(p)==h,'fixed input '+p)
 need(sha(PRE/'CHECK.json')=='6f5f1901bf0084be02fb7e8ad0783f60c93f67d5e6fac3a7628da89f4047ad99' and json.loads((PRE/'CHECK.json').read_bytes())['driver_sha256']==DRIVER,'prelaunch audit')
 q=subprocess.run([sys.executable,'-I','-S','-B',str(PARENT/'audit.py')],capture_output=True,timeout=900);need(q.returncode==0 and not q.stderr and json.loads(q.stdout)==json.loads((PARENT/'CHECK.json').read_bytes()),'saturation parent audit')
 need(sha(PLAN_AUDIT/'CHECK.json')=='47bd9296128571350c0d4f54d7cb0940206b1e6c96a7b8e4cbb2dd4cddbd9191','historical closure audit receipt')
 old=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN_AUDIT/'audit.py')],capture_output=True,timeout=900)
 need(old.returncode==1 and b'ValueError: committed bytes ' in old.stderr and b'FreeJConcreteDigitsClient.lean' in old.stderr,'historical draft drift guard')
 draft=PKG/'FreeJConcreteDigitsClient.lean';blob=subprocess.run(['git','show','b8dd85dd7d:'+draft.relative_to(ROOT).as_posix()],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
 need(hashlib.sha256(blob).hexdigest()=='4cc03af96d0f130f133c546ca653881a985d9c721ffe6f146ddb2ced7e250e08' and sha(draft)=='e859356894c307fffaf349ca65d6a0b40478201c95571d5b660f099816a2f52d','old and corrected client hashes')
 fresh=subprocess.run([sys.executable,'-I','-S','-B',str(PLAN/'scan.py')],capture_output=True,timeout=120)
 need(fresh.returncode==0 and not fresh.stderr and fresh.stdout==(PLAN/'scan.json').read_bytes(),'independent current source scan')
 need(rec['saturation_audit']==json.loads((PARENT/'CHECK.json').read_bytes()),'saturation receipt')
 scan=json.loads((PLAN/'scan.json').read_bytes());rows=scan['modules'];need(len(rows)==12,'source closure')
 modules=[x['module'] for x in rows]+['DiophantineConsistency.FreeJConcreteDigitsClient'];src_hash={x['module']:x['source_sha256'] for x in rows};src_hash[modules[-1]]=rec['fixed_inputs_sha256'][str(PKG/'FreeJConcreteDigitsClient.lean')]
 allruns=[]
 for run,side in zip(rec['runs'],('author','peer')):
  need(run['label']==side and [x['module'] for x in run['steps']]==modules,'module order')
  lib=OUT/side/'lib';base=PREFIX/side/'lib';orig={p.relative_to(base) for p in base.rglob('*.olean')};actual={p.relative_to(lib) for p in lib.rglob('*.olean')};extra={Path(*n.split('.')).with_suffix('.olean') for n in modules}
  need(len(orig)==114 and not orig&extra and actual==orig|extra,'overlay inventory')
  for rel in orig:need((lib/rel).resolve()==(base/rel).resolve() and sha(lib/rel)==sha(base/rel),'provider '+str(rel))
  available=set(orig);steps=[];report_count=0
  for ix,row in enumerate(run['steps']):
   name=row['module'];rel=Path(*name.split('.'));src=OUT/'frozen'/rel.with_suffix('.lean');obj=lib/rel.with_suffix('.olean');log=OUT/side/(name.replace('.','_')+'.log');copy=PKG/'evidence'/side/log.name
   need(row['compiler_exit']==row['deps_exit']==0 and row['stop_reason'] is None,'child exits '+name)
   need(sha(src)==row['source_sha256']==src_hash[name] and sha(obj)==row['object_sha256'] and sha(log)==sha(copy)==row['log_sha256'] and log.read_text()==row['stdout'],'artifacts '+name)
   cmd=row['command'];need(cmd[1:4]==['-M3000','-j1','-DElab.async=false'] and cmd[-3]==str(src) and cmd[-1]==str(obj),'command '+name)
   imports=[v for l in src.read_text().splitlines() if l.startswith('import ') for v in l[7:].split()]
   if ix<12:need(imports==rows[ix]['imports'],'frozen import list '+name)
   deps={str(PACKAGE/'Init.olean')}
   for dep in imports:
    drel=Path(*dep.split('.')).with_suffix('.olean')
    if dep.startswith('DiophantineConsistency.'):
     need(drel in available,'same-side missing '+name+':'+dep);candidate=lib/drel
    elif drel in available:candidate=lib/drel
    else:candidate=PACKAGE/drel
    need(candidate.is_file(),'dependency '+dep);deps.add(str(candidate))
   need(set(row['deps_stdout'].splitlines())==deps,'direct imports '+name)
   reports=re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$",row['stdout'],re.M);wanted=re.findall(r'^#print axioms\s+([^\s]+)',src.read_text(),re.M)
   need([n for n,_ in reports]==wanted and [[n,a] for n,a in reports]==row['axiom_reports'],'exact report names '+name)
   need(all({x.strip() for x in ax.split(',')}=={'propext','Classical.choice','Quot.sound'} for _,ax in reports),'axiom sets '+name)
   need(not re.search(r'warning:|error:|\bsorryAx\b|\bsorry\b',row['stdout']),'warning/error '+name)
   report_count+=len(reports);available.add(rel.with_suffix('.olean'));steps.append({'module':name,'source_sha256':row['source_sha256'],'object_sha256':row['object_sha256'],'log_sha256':row['log_sha256'],'recorded_compiler_exit':0,'recorded_deps_exit':0})
  need(report_count==19,'named axiom report count');allruns.append({'side':side,'steps':steps,'axiom_reports':report_count})
 need(allruns[0]['steps']==allruns[1]['steps'],'sibling outputs')
 print(json.dumps({'status':'PASS_INDEPENDENT_FREEJ_CONCRETE_DIGITS_CLIENT_AUDIT','evidence_commit':'04f0521ce9','receipt_sha256':R,'recorded_outer_session':32593,'recorded_outer_exit':0,'reported_launch_head':'23bd9093c8f39484082859c59737e6406dca2552','saturation_parent_audit_rerun_exit':q.returncode,'historical_closure_audit_current_rerun_exit':old.returncode,'historical_draft_sha256':'4cc03af96d0f130f133c546ca653881a985d9c721ffe6f146ddb2ced7e250e08','corrected_client_sha256':sha(draft),'fresh_source_closure_scan_exit':fresh.returncode,'steps_per_side':13,'axiom_reports_per_side':19,'runs':allruns,'scope':'Conditional IΣ₁ graph digit bound with explicit symbolic low-port equality, graph/radix/mask assumptions; no retained-MC binding, machine/checker or PRA proof; inherited provider/resource limits.'},indent=2))
if __name__=='__main__':main()
