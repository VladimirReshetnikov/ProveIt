#!/usr/bin/env python3
"""Independent read-only audit of terminal K216 records; never replays supplied code."""
from pathlib import Path
import argparse,gzip,hashlib,json
ap=argparse.ArgumentParser();ap.add_argument('--records',type=Path,required=True);ap.add_argument('--packet',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
R=a.records.resolve();P=a.packet.resolve();pins={};checks=0

def need(c,s):
 global checks
 checks+=1
 if not c:raise AssertionError(s)

def raw(p):
 p=Path(p)
 if not p.exists():p=Path(str(p)+'.gz')
 b=p.read_bytes();pins[str(p)]={'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)}
 return gzip.decompress(b)if p.suffix=='.gz'else b

def obj(p):return json.loads(raw(p))
def digest(p):return hashlib.sha256(raw(p)).hexdigest()
def text(p):return raw(p).decode()

def table(p,halt):
 T={};start=None
 for l in text(p).splitlines():
  if l.startswith('#! start '):start=int(l[9:]);continue
  if not l or l.startswith('#'):continue
  q,b,w,d,z=l.split();q,b,w,z=map(int,(q,b,w,z))
  need((q,b)not in T and b in(0,1)and w in(0,1)and d in('L','R'),'table row');T[q,b]=(w,1 if d=='R'else-1,z)
 Q={q for q,b in T};need(set(T)=={(q,b)for q in Q for b in(0,1)}and start==0 and halt not in Q and all(z in Q|{halt}for w,d,z in T.values()),'total table with exact start/halt')
 return T,Q

actual=obj(R/'actual.json');need(actual['status']=='FIVE_SELECTED_LEAVES_PASS','terminal actual record required')
expected=[('reconstruct','reconstruct216.py','EXACT_SOURCE_AND_TABLE_RECONSTRUCTION_PASS',60),('source','source_equivalence.py','ALL_NATURAL_SOURCE_BISIMULATION_PASS',60),('blank-marker','audit216.py','MARKER_LEMMA_CANONICAL_ISOMORPHISM_AND_WHOLE_BLANK_PASS',60),('local-fold','check_joint_fold.py','INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS',90),('runtime','validate_native.py','UNIVERSAL_MATHEMATICAL_PASS',360)]
need([j['name']for j in actual['jobs']]==[x[0]for x in expected],'all five ordered selected jobs')
first=actual['jobs'][0];oldout=Path(first['argv'][-1]).parent;oldpacket=Path(first['cwd']);oldparent=Path(first['argv'][4])
argv_expected=[['--parent',str(oldparent),'--out',str(oldout/'rebuilt')],['--baseline',str(oldparent/'machine/sites217.json'),'--candidate',str(oldpacket/'source/sites216.json'),'--out',str(oldout/'source')],['--out',str(oldout/'blank-marker.json')],['--old',str(oldpacket/'machine/prefold217.native.tm'),'--new',str(oldpacket/'machine/k216.native.tm'),'--keep','164','--drop','183','--radius','4','--fuel','20','--output',str(oldout/'fold-window.json')],[str(oldpacket/'machine/k216.native.tm'),str(oldpacket/'source/sites216.json'),str(oldout/'runtime')]]
for j,(name,script,status,cap),tail in zip(actual['jobs'],expected,argv_expected):
 need(j['exit_code']==0 and j['timed_out']is False and j['accepted']is True and j['status']==status,'successful exact job '+name)
 need(j['timeout_seconds']==cap and 0<=j['seconds']<=cap+10,'recorded bounded execution '+name)
 need(j['argv'][1:]==['-B',str(oldpacket/'code'/script)]+tail and Path(j['argv'][0]).name.startswith('python'),'literal command tokens '+name)
 need(j['cwd']==str(oldpacket),'same disposable packet working directory')
 log=text(R/'logs'/f'{name}.stdout');err=text(R/'logs'/f'{name}.stderr')
 need(not err.strip() and status in log,'raw terminal log '+name)
 digest(P/'code'/script)
# Exact immutable table/source inputs and all rebuilt bytes.
fixed={'machine/k216.native.tm':'2efb7adf9cfcbea58197a2bde2610b22f58b647f05385bc716b036242be6fa6c','machine/k216.tm':'5536fcf48e76f56152cfa0a77cae19c09be7161d39514075522ecfe056cffc45','machine/prefold217.native.tm':'6cb717fe9e80be907fc80d5b85b0f36d35242dfde4723d4589ecddd2802eaae1','source/sites216.json':'c865047ce7283521199e93ce74307821f3b3231742213329b7ac5e8a7ec0b6d2','source/sites216.compact.json':'7f9d4f321b7a7d56013056b1ad6be2723538c43ea2d73548bcd0e35f0381bde0'}
for f,h in fixed.items():
 need(digest(P/f)==h,'fixed packet identity '+f)
 need(raw(R/'rebuilt'/Path(f).name)==raw(P/f),'exact rebuilt output '+f)
codepins={'reconstruct216.py':'69c6df8bdbf45adef5f6b2661fc429db85d4a7fc46a7ef8b22b9cae220ac6ee4','source_equivalence.py':'57d6316baa7e491bca65b91ec76b72e3d8f8f8d1f08145d33f22949b300d227e','audit216.py':'9556114bb4a56d32b4f0c1261ed77ea93d8a45f44a7f18c5fd02c22e893f0dde','check_joint_fold.py':'82d0b364dfdbc7433a58c3c3e7166ec6a32ac9268e0e516f5f113f1287f44031','validate_native.py':'49b0a77bafa3549cef72e381352eeadad28937519ec5463c3cf3bee545f6f7e2','runtime/symbolic_runtime.py':'7ca30fd11def00e973d8f30997e51fa2dd87ae2eff311ea8c9fc4ac08c9d774f','runtime/independent_runtime.py':'0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346','inputs/legacy_mapping.json':'26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf'}
for f,h in codepins.items():need(digest(P/'code'/f)==h,'reviewed code identity '+f)
T,Q=table(P/'machine/k216.native.tm',254);C,CQ=table(P/'machine/k216.tm',216)
need(len(Q)==216 and len(T)==432 and CQ==set(range(216)),'216/432 machine census')
mp=obj(P/'machine/canonicalization.json');m={int(k):v for k,v in mp['native_to_canonical'].items()}
need(set(m)==Q|{254}and set(m.values())==set(range(217))and len(m)==217 and m[0]==0 and m[254]==216 and m[84]==84,'exact canonical bijection')
need({(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in T.items()}==C,'every canonical row')
sites=obj(P/'source/sites216.json');need(sites==obj(P/'source/sites216.compact.json'),'source serializers agree')
for name in('recipe.json','ordinal_correspondence.json','verification.json'):
 need(raw(R/'source'/name)==raw(P/'evidence'/('source_'+name)),'exact source output '+name)
src=obj(R/'source/verification.json');need(src['status']==expected[1][2]and src['guarded_successors']==6175 and src['first37_and_nonAX_unchanged']is True,'full source gate')
need(src['candidate_raw_source_sha256']==fixed['source/sites216.json']and src['candidate_canonical_source_sha256']==fixed['source/sites216.compact.json']and src['verifier_sha256']==digest(P/'code/source_equivalence.py'),'source identity gates')
need(src['recipe_sha256']==digest(R/'source/recipe.json')and src['correspondence_sha256']==digest(R/'source/ordinal_correspondence.json'),'recipe and ordinal bindings')
# Fold result is deterministic except elapsed seconds.
fold=obj(R/'fold-window.json');oldfold=obj(P/'evidence/fold-window.json')
need({k:v for k,v in fold.items()if k!='seconds'}=={k:v for k,v in oldfold.items()if k!='seconds'},'fresh fold identity')
need(fold['status']==expected[3][2]and fold['old_states']==217 and fold['new_states']==216 and fold['keep']==164 and fold['drop']==183 and fold['radius']==4 and fold['fuel']==20,'literal fold contract')
need(fold['inductive_window_contexts']==27527 and fold['nontrivial_contexts']==48 and fold['positive_old_new_block_histogram']==[[1,1,27479],[1,3,48]],'positive fold context census')
need(fold['negative_control']['status']=='REJECTED'and 'new halt without proved old halt'in fold['negative_control']['reason'],'corrupted initial halt control')
need(fold['checker_sha256']==digest(P/'code/check_joint_fold.py')and fold['old_sha256']==fixed['machine/prefold217.native.tm']and fold['new_sha256']==fixed['machine/k216.native.tm'],'fold input identities')
blank=obj(R/'blank-marker.json');need(blank['status']==expected[2][2]and blank['working_states']==216 and blank['rows']==432 and blank['graph_reachable_working_states']==216,'blank marker result')
need(blank['incoming_origin_guards']=={'164':[[143,1,1,'R']],'183':[[205,0,0,'R']]},'literal incoming origin guards')
# Full startup equality includes every newly recomputed trace row and one-cell coordinate.
startup=obj(R/'runtime/startup.json');delivered_startup=obj(P/'evidence/startup.json')
need(startup==delivered_startup,'fresh whole startup identical to delivered full trace and frame')
need(startup['status']=='CALIBRATED_DIRTY_ROOT_SEED'and(startup['steps'],startup['state'],startup['head'],startup['gap'],startup['registers'],startup['spares'])==(313133,84,-5,80,[3,0,0,0,3,0,0,0,0],[1]*130),'exact calibrated root frame')
need(len(startup['trace'])==313133 and len(startup['one_cells'])==len(set(startup['one_cells']))==277,'complete recorded prefix/support')
need(blank['blank_steps']==313133 and blank['head']==-5 and blank['native_dispatch']==blank['canonical_dispatch']==84 and blank['one_cells']==startup['one_cells'],'independent native/dense blank result joins runtime startup')
need('STARTUP CALIBRATED_DIRTY_ROOT_SEED 313133'in text(R/'logs/runtime.stdout'),'literal startup stdout token')
# Full quantified runtime. No symbolic interpreter or supplied checker is invoked here.
runtime=obj(R/'runtime/runtime.json');delivered=obj(P/'evidence/runtime.json');cases=obj(R/'runtime/runtime_cases.json');saved=obj(P/'evidence/runtime_cases.json')
need(runtime['status']=='UNIVERSAL_MATHEMATICAL_PASS'and runtime['proved_cases']==runtime['expected_cases']==6176 and runtime['site_count']==4751 and runtime['working_states']==216 and runtime['failures']==[],'full runtime gate')
need({k:v for k,v in runtime.items()if k!='seconds'}=={k:v for k,v in delivered.items()if k!='seconds'},'runtime receipt equality except timing')
need(cases==saved,'every ordered fresh runtime case equals delivered case')
need([(x['site_index'],x['positive'])for x in cases]==[(i,p)for i,row in enumerate(sites)for p in((False,True)if row[1]=='CD'else(False,))],'every guard present exactly once in source order')
for c in cases:need(len(c['duration'])==13 and c['duration'][0]>0 and all(type(v)is int and v>=0 for v in c['duration']),'positive nonnegative integer affine duration')
need(sum(c['symbolic_steps']for c in cases)==1709992 and min(c['duration'][0]for c in cases)==13,'symbolic rule and positive duration totals')
for field,f in [('table_sha256','machine/k216.native.tm'),('sites_sha256','source/sites216.json'),('checker_sha256','code/runtime/symbolic_runtime.py'),('helper_sha256','code/runtime/independent_runtime.py')]:need(runtime[field]==digest(P/f),'runtime bound '+field)
lm={int(k):int(v)for k,v in obj(P/'code/inputs/legacy_mapping.json').items()}
for q in Q|{254}:lm.setdefault(q,q+1000)
need(len({lm[q]for q in Q|{254}})==217,'injective exact current legacy relabeling')
L={(lm[q],b):(w,d,lm[z])for(q,b),(w,d,z)in T.items()};rev={lm[q]:q for q in Q}
blocks=runtime['blocks'];need(len(blocks)==4 and [(x['entry'],x['direction'],x['before'],x['after'])for x in blocks]==[(73,1,'B','B'),(95,1,'B','C'),(48,-1,'B','B'),(112,-1,'C','B')],'all four exact-table list block schemas')
cover={tuple(r)for c in cases for r in c['rows']}
for block in blocks:
 need(block['steps']=='v+2'and block['arbitrary_contexts']is True,'symbolic one-block contract')
 for ev in block['trace']:
  need(ev[0]in('literal','unary'),'block trace uses direct/unary rules')
  q,b,w,d,z=ev[1];need(L[q,b]==(w,d,z),'block literal row binding');cover.add((q,b))
need({(rev[q],b)for q,b in cover}==set(T),'all432 table rows covered by full cases and block traces')
need(all(tuple(r)in L for c in cases for r in c['rows']),'each reported case row is defined')
digest(Path(__file__))
result=dict(status='INDEPENDENT_FRESH_K216_RECORD_AUDIT_PASS',findings=[],checks=checks,actual_record_sha256=pins[str(R/'actual.json')]['sha256'],working_states=216,transition_rows=432,source=dict(leaves=4751,dag_nodes=203,guarded_edges=6175,guarded_cases=6176),runtime=dict(cases=6176,symbolic_rules=1709992,minimum_affine_duration=13,covered_rows=432,seconds=runtime['seconds']),startup=dict(steps=313133,native_dispatch=84,canonical_dispatch=84,head=-5,gap=80,registers=startup['registers'],spares=130,one_cells=277,full_fresh_trace_equal=True),scope='Independent read-only audit of five terminal fresh jobs, exact raw outputs and input identities. No supplied execution, compiler, machine simulation, or new symbolic derivation by this reviewer. Inherited mathematical calibration and prior source/physical reviews remain separate.',authorship='opening_encoder authored the earlier static review and five-leaf proposal plus this record auditor. Root selected/executed the actual five jobs. The submitted216 construction is independently attributed.',inputs=pins)
a.output.parent.mkdir(parents=True,exist_ok=True)
with a.output.open('x')as f:f.write(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:v for k,v in result.items()if k!='inputs'},indent=2))
