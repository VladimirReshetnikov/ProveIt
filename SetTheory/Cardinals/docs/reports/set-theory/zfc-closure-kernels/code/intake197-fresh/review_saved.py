#!/usr/bin/env python3
"""Read saved Source159 outputs only. Never import or execute candidate code.

Portable with --run preserving the recorded output layout and --packet naming
an independently recovered pristine packet. Absolute historical argv/receipt
paths are rebased from the recorded packet cwd. No process replay occurs.
"""
import argparse,gzip,hashlib,json
from pathlib import Path

PINS={
 'validate_native.py':'49b0a77bafa3549cef72e381352eeadad28937519ec5463c3cf3bee545f6f7e2',
 'runtime/symbolic_runtime.py':'7ca30fd11def00e973d8f30997e51fa2dd87ae2eff311ea8c9fc4ac08c9d774f',
 'runtime/independent_runtime.py':'0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346',
 'inputs/legacy_mapping.json':'26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf'}
PH=(6,2,0,4,3,7,8,5,1)
ROOT217='parents/K217_Dominated_Continuation_2026-10-20'
ROOT149='parents/K218_Dominated_Rho8_2026-10-20'

def need(p,m):
 if not p:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(gzip.decompress(p.read_bytes()) if p.suffix=='.gz' else p.read_bytes())
def raw(p):return gzip.decompress(p.read_bytes()) if p.suffix=='.gz' else p.read_bytes()
def table(path):
 t={}
 for line in path.read_text().splitlines():
  if not line.strip() or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
  need((q,b) not in t and b in (0,1) and w in (0,1) and d in ('L','R'),'literal table format')
  t[q,b]=(w,1 if d=='R' else -1,z)
 return t

def expected_frame():
 physical=[0]*9
 for i,j in enumerate(PH):physical[j]=[4,0,0,0,0,0,0,0,0][i]
 one={-9,57};p=58
 for v in physical+[1]*40:
  one.update(range(p+1,p+v+2));p+=v+2
 need(len(one)==95,'own frame census');return sorted(one)

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--run',type=Path,required=True);ap.add_argument('--packet',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
 a=ap.parse_args();R=a.run.resolve();P=a.packet.resolve();actual=read(R/'actual.json')
 need(actual['status']=='TEN_SELECTED_LEAVES_PASS','terminal aggregate PASS required')
 names=['source-build','permutation210','permutation120','independent-source','table-build','machine-audit','blank210','blank120','runtime210','runtime120']
 jobs=actual['jobs'];need([j['name'] for j in jobs]==names,'exact ordered ten jobs')
 prior=Path(jobs[0]['cwd']).parent
 def norm(s):
  try:return str(Path(s).relative_to(prior))
  except ValueError:return '@secondary_blank.py' if Path(s).name=='secondary_blank.py' else s
 B=ROOT217;G=ROOT149+'/binary/code';Q='packet'
 expected=[
 ['packet/code/build_sources.py','--baseline219',Q+'/source/baseline219.json','--baseline217',B+'/machine/sites217.json','--output','rebuilt-sources'],
 ['packet/code/audit_command_permutation.py','--baseline219',Q+'/source/baseline219.json','--frozen202',Q+'/source/frozen202.json','--candidate',Q+'/machine/sites216.json','--permutation','210','--output','source210.json'],
 ['packet/code/audit_command_permutation.py','--baseline219',Q+'/source/baseline219.json','--frozen202',Q+'/source/frozen202.json','--candidate',Q+'/secondary/sites120.json','--permutation','120','--output','source120.json'],
 ['packet/code/audit_source210.py',Q+'/source/reference205.json',Q+'/source/frozen202.json',Q+'/machine/sites216.json',B+'/code/vendor/source_language.py','independent-source.json'],
 ['packet/code/reconstruct.py','--baseline217',B+'/machine/k217.native.tm','--output','rebuilt-tables'],
 ['machine-audit/audit.py'],['packet/code/audit_blank210.py',Q+'/machine/k216.native.tm','startup210.json','blank210.json'],
 ['@secondary_blank.py','--packet','packet','--output','blank120.json'],
 [G+'/validate_native.py',Q+'/machine/k216.native.tm',Q+'/machine/sites216.json','runtime210'],
 [G+'/validate_native.py',Q+'/secondary/k216-120.native.tm',Q+'/secondary/sites120.json','runtime120']]
 receipts=['rebuilt-sources/source_build.json','source210.json','source120.json','independent-source.json','rebuilt-tables/reconstruction.json','machine-audit/audit.json','blank210.json','blank120.json','runtime210/runtime.json','runtime120/runtime.json']
 statuses=['PASS_DETERMINISTIC_SOURCE_REBUILD','PASS_EXACT_SOURCE_COMMAND_PERMUTATION','PASS_EXACT_SOURCE_COMMAND_PERMUTATION','PASS','PASS_EXACT_TABLE_RECONSTRUCTION','PASS','PASS','INDEPENDENT_SECONDARY_NATIVE_CANONICAL_BLANK_PASS','UNIVERSAL_MATHEMATICAL_PASS','UNIVERSAL_MATHEMATICAL_PASS']
 logs={};processes=[]
 for j,args,receipt,status in zip(jobs,expected,receipts,statuses):
  need(j['accepted'] is True and j['exit_code']==0 and j['timed_out'] is False,'successful process '+j['name'])
  need(j['timeout_seconds']==(360 if j['name'].startswith('runtime') else 90),'wall cap')
  need(0<=j['seconds']<j['timeout_seconds'],'recorded elapsed time')
  need(j['argv'][1]=='-B' and [norm(s) for s in j['argv'][2:]]==args,'exact selected argv '+j['name'])
  need(norm(j['cwd'])=='packet' and norm(j['receipt'])==receipt,'cwd and receipt binding')
  need(j['status']==status and read(R/receipt)['status']==status,'receipt status')
  out=R/'logs'/(j['name']+'.stdout');err=R/'logs'/(j['name']+'.stderr')
  need(out.stat().st_size>0 and err.read_bytes()==b'','nonempty stdout / empty stderr')
  need('Traceback' not in out.read_text() and 'NOT_PROVED' not in out.read_text(),'no hidden failure in stdout')
  if j['name'].startswith('runtime'):need('UNIVERSAL_MATHEMATICAL_PASS' in out.read_text(),'runtime terminal log')
  logs[j['name']]={'stdout_sha256':sha(out),'stderr_sha256':sha(err),'receipt_sha256':sha(R/receipt)}
  processes.append({'name':j['name'],'seconds':j['seconds'],'wall_cap':j['timeout_seconds']})
 # Selected delivered inputs equal the pristine recovery, not a blanket
 # historical before/after claim (the root runner did not capture that map).
 selected=['code/build_sources.py','code/audit_command_permutation.py','code/audit_source210.py','code/reconstruct.py','code/audit_blank210.py','source/baseline219.json','source/reference205.json','source/frozen202.json','machine/sites216.json','machine/k216.native.tm','machine/k216.tm','machine/audit.py','secondary/sites120.json','secondary/k216-120.native.tm','secondary/k216-120.tm','provenance/transition_recipe210.json','provenance/transition_recipe120.json']
 for s in selected:need((R/'packet'/s).read_bytes()==(P/s).read_bytes(),'pristine input '+s)
 for s,h in PINS.items():need(sha(R/G/s)==h,'inherited runtime input '+s)
 need(sha(R/B/'code/vendor/source_language.py')=='4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f','source helper')
 for x,y in [('sites205_reference.json','source/reference205.json'),('sites202.json','source/frozen202.json'),('sites210.json','machine/sites216.json'),('sites120.json','secondary/sites120.json')]:need((R/'rebuilt-sources'/x).read_bytes()==(P/y).read_bytes(),'exact rebuilt source '+x)
 for x,y in [('k216-210.native.tm','machine/k216.native.tm'),('k216-210.tm','machine/k216.tm'),('k216-120.native.tm','secondary/k216-120.native.tm'),('k216-120.tm','secondary/k216-120.tm')]:need((R/'rebuilt-tables'/x).read_bytes()==(P/y).read_bytes(),'exact rebuilt table '+x)
 for s in ['k216.tm','canonicalization.json','blank-prefix.json.gz','blank-seed.json','local81-proof.json','full_table.tex','audit.json']:need(raw(R/'machine-audit'/s)==raw(P/'machine'/s),'machine regeneration '+s)
 for perm in ('210','120'):
  d=read(R/f'source{perm}.json');need(d['candidate_metrics']==dict(dag_nodes=202,leaf_occurrences=4751,guarded_cases=6176,maximum_depth=44,maximum_zero_run=6),'source metrics')
  need(d['AX_subtree_unchanged'] is True and d['literal_external_primitive_occurrences']==4593 and d['body_boundary_demands']==[[0,0]]*3,'closed literal body scope')
  commands=['NIP','DROP','MP','AX'] if perm=='210' else ['DROP','NIP','MP','AX']
  need([x['command'] for x in d['selector_partition']]==commands,'exact selector partition')
  need(d['wire_fields']['AX']==['c+3','y','x'] and d['wire_fields']['MP']==[2,'x'],'wire formats')
  need(d['cofinal_padding_packing']==['P',3,['P','Y',['P',1,'R']]],'cofinal first candidate')
  need(all(x['final_target']==0 for x in d['normal_return_routes']),'normal return routes')
 ind=read(R/'independent-source.json');need(ind['noncommon202_matches_reference_primitive_word'] and ind['noncommon202_matches_reference_complete_guarded_ordinal_CFG'] and ind['exterior_source_identical'] and ind['source210_independent_CFG_resolvers_agree'],'independent source scope')
 one=expected_frame();runtime={}
 for perm,native,canon,sites,stored,rules,minimum,steps in [
 ('210','machine/k216.native.tm','machine/k216.tm','machine/sites216.json','evidence',1605450,6,95674),
 ('120','secondary/k216-120.native.tm','secondary/k216-120.tm','secondary/sites120.json','secondary',1605505,9,96244)]:
  T=table(P/native);C=table(P/canon);states={q for q,b in T}
  need(len(states)==216 and len(T)==432 and set(T)=={(q,b) for q in states for b in (0,1)},'native census/totality')
  need({z for w,d,z in T.values()}-states=={254},'native halt')
  dense={q:i for i,q in enumerate(sorted(states))};dense[254]=216
  need(dense[0]==0 and dense[84]==83 and {(dense[q],b):(w,d,dense[z]) for (q,b),(w,d,z) in T.items()}==C,'all432 canonical row bindings')
  m={int(q):v for q,v in read(R/G/'inputs/legacy_mapping.json').items()}
  for q in states|{254}:
   if q not in m:m[q]=q+1000
  need(len({m[q] for q in states|{254}})==217,'legacy mapping injective')
  L={(m[q],b):(w,d,m[z]) for (q,b),(w,d,z) in T.items()}
  rep=read(R/f'runtime{perm}/runtime.json');cases=read(R/f'runtime{perm}/runtime_cases.json');st=read(R/f'runtime{perm}/startup.json');ss=read(P/sites)
  need(rep['status']=='UNIVERSAL_MATHEMATICAL_PASS' and rep['failures']==[] and rep['proved_cases']==rep['expected_cases']==6176 and rep['working_states']==216 and rep['site_count']==4751,'runtime status/census')
  need(rep['table_sha256']==sha(P/native) and rep['sites_sha256']==sha(P/sites) and rep['checker_sha256']==PINS['runtime/symbolic_runtime.py'] and rep['helper_sha256']==PINS['runtime/independent_runtime.py'],'exact runtime inputs')
  wanted=[(i,pos) for i,(_,op,k) in enumerate(ss) for pos in ((False,True) if op=='CD' else (False,))]
  need(len(ss)==4751 and sum(x[1]=='CD' for x in ss)==1425 and [(c['site_index'],c['positive']) for c in cases]==wanted,'exact ordered6176 guards')
  used=set()
  for c in cases:
   need(len(c['duration'])==13 and all(type(v) is int and v>=0 for v in c['duration']) and c['duration'][0]>0,'positive affine duration')
   need(len(c['motion'])==13 and all(type(v) is int for v in c['motion']),'affine motion shape')
   need(c['symbolic_steps']>0 and sum(c['kinds'].values())==c['symbolic_steps'],'symbolic event census')
   for row in c['rows']:need(tuple(row) in L,'case row is bound to literal table');used.add(tuple(row))
  need(sum(c['symbolic_steps'] for c in cases)==rules and min(c['duration'][0] for c in cases)==minimum,'exact rules/minimum')
  blockkeys=[];blockrows=set()
  for b in rep['blocks']:
   blockkeys.append((b['entry'],b['direction'],b['before'],b['after']))
   need(b['steps']=='v+2' and b['arbitrary_contexts'] is True,'whole-context block scope')
   for ev in b['trace']:
    need(ev[0] in ('literal','unary') and len(ev[1])==5,'block event shape')
    q,bit,w,d,z=ev[1];need(L[q,bit]==(w,d,z),'block exact literal action');blockrows.add((q,bit))
  need(blockkeys==[(73,1,'B','B'),(95,1,'B','C'),(48,-1,'B','B'),(112,-1,'C','B')],'four expected block schemas')
  need(used|blockrows==set(L) and len(used|blockrows)==432,'all432 exact runtime rows including blocks')
  need(cases==read(P/stored/'runtime_cases.json.gz'),'fresh ordered cases equal delivered')
  delivered=read(P/stored/'runtime.json');need({k:v for k,v in rep.items() if k!='seconds'}=={k:v for k,v in delivered.items() if k!='seconds'},'runtime semantic receipt equality')
  need(st==read(P/stored/'startup.json.gz'),'fresh complete startup receipt equality')
  need(st['status']==rep['startup_status']=='CALIBRATED_DIRTY_ROOT_SEED' and st['steps']==len(st['trace'])==steps,'startup count/status')
  need(st['state']==84 and st['head']==-8 and st['gap']==1 and st['registers']==[4,0,0,0,0,0,0,0,0] and st['spares']==[1]*40 and st['one_cells']==one,'complete direct expected frame')
  # Static certificate consistency only: row/head chaining, no tape simulation.
  prevq,prevh=0,0
  for event in st['trace']:
   q,h,b,w,d,z=event;need((q,h)==(prevq,prevh) and T[q,b]==(w,d,z),'stored trace row/head linkage');prevq,prevh=z,h+d
  need((prevq,prevh)==(84,-8),'stored trace terminal linkage')
  runtime[perm]={'cases':len(cases),'symbolic_rules':rules,'min_positive_constant':minimum,'rows':432,'block_rows':len(blockrows),'startup_steps':steps,'one_cells':95,'gap':1,'runtime_seconds':rep['seconds'],'cases_sha256':sha(R/f'runtime{perm}/runtime_cases.json'),'startup_sha256':sha(R/f'runtime{perm}/startup.json')}
 b=read(R/'blank210.json');need(b['whole_tape_one_cells']==one and b['logical_registers']==[4,0,0,0,0,0,0,0,0] and b['spares']==[1]*40 and b['blank_steps']==95674 and b['whole_tape_equal_to_direct_frame_construction'] and b['trace_equal_to_separate_sparse_simulator'],'independent primary blank')
 b=read(R/'blank120.json');need(b['one_cells']==one and b['steps']==96244 and b['registers']==[4,0,0,0,0,0,0,0,0] and b['spares']==40 and b['gap']==1 and b['complete_trace_compared'],'independent secondary blank')
 result={'status':'PASS_INDEPENDENT_SAVED_OUTPUT_AUDIT','actual_sha256':sha(R/'actual.json'),'auditor_sha256':sha(Path(__file__)),'scope':'Read-only saved outputs, log/process metadata, current pristine selected input equality, exact source/table/canonical artifacts, all ordered runtime guards/row references/block actions/affine census, fresh-vs-delivered equality and whole startup endpoint. No candidate replay, no new proof of symbolic induction soundness, no historical before-map claim.','processes':processes,'runtime':runtime,'logs':logs,'selected_pristine_inputs':{s:sha(P/s) for s in selected},'runtime_inputs':PINS,'limitations':['The runner records no separate before/after input hash map; this audit compares selected current disposable inputs to the pristine packet and reviewed inherited pins.','Read-only trace consistency checks do not replace the two actual independent tape replays.','Inherited numerical calibration and ordinary induction-rule soundness remain separate reviewed premises.']}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n');print(result['status']);print(json.dumps(runtime,indent=2))
if __name__=='__main__':main()
