#!/usr/bin/env python3
"""Independent saved215 audit and approved finite native/canonical blank replay.

No supplied Python imports, symbolic runtime rerun or compiler. Invoke only after
root observes terminal PASS. --run may be a relocated copy retaining its layout.
"""
from pathlib import Path
import argparse,hashlib,json,time
PINS={
 'code/validate_native.py':'49b0a77bafa3549cef72e381352eeadad28937519ec5463c3cf3bee545f6f7e2',
 'code/runtime/symbolic_runtime.py':'7ca30fd11def00e973d8f30997e51fa2dd87ae2eff311ea8c9fc4ac08c9d774f',
 'code/runtime/independent_runtime.py':'0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346',
 'code/inputs/legacy_mapping.json':'26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf',
 'candidate.native.tm':'9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2',
 'sites.json':'17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba',
 'candidate.tm':'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090',
 'canonicalization.json':'c24abea425721f9b2d5cb7bbb1a2e9b164b4f3837e362c7ca4c3a88da6ac885a'}

def need(ok,m):
 if not ok:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_bytes())
def table(path,halt):
 t={}
 for l in path.read_text().splitlines():
  if not l.strip() or l.startswith('#'):continue
  q,b,w,d,z=l.split();q,b,w,z=map(int,(q,b,w,z))
  need((q,b)not in t and min(q,z)>=0 and b in (0,1) and w in (0,1) and d in ('L','R'),'row syntax')
  t[q,b]=(w,1 if d=='R' else -1,z)
 states={q for q,b in t}
 need(len(states)==215 and len(t)==430 and set(t)=={(q,b)for q in states for b in (0,1)},'215state total table')
 need(0 in states and {z for w,d,z in t.values()}-states=={halt},'start and sole external halt')
 return t

def expected_frame():
 logical=[4,0,0,0,0,0,0,0,0];physical=[0]*9
 for i,j in enumerate((6,2,0,4,3,7,8,5,1)):physical[j]=logical[i]
 ones={-9,57};pos=58
 for v in physical+[1]*40:
  ones.update(range(pos+1,pos+v+2));pos+=v+2
 need(len(ones)==95,'direct frame census');return ones

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
 a=ap.parse_args();R=a.run.resolve();began=time.monotonic();actual=read(R/'actual.json')
 need(actual['status']=='PASS' and actual['returncode']==0 and actual['timed_out'] is False,'terminal root PASS')
 need(actual['timeout_seconds']==360 and 0<actual['elapsed_seconds']<360,'bounded runtime process')
 need(actual['before']==actual['after']==read(R/'before.json')==PINS,'exact before/after pins')
 for rel,pin in PINS.items():need(sha(R/rel)==pin,'current unchanged input '+rel)
 argv=actual['argv'];need(argv[1]=='-B','assertion-enabled direct runtime invocation')
 prior=Path(argv[2]).parent.parent
 need([str(Path(x).relative_to(prior))for x in argv[2:]]==['code/validate_native.py','candidate.native.tm','sites.json','runtime'],'exact supplied process argv')
 log=(R/'runtime.log').read_text();need('UNIVERSAL_MATHEMATICAL_PASS' in log and 'NOT_PROVED' not in log and 'Traceback'not in log,'raw runtime terminal log')
 T=table(R/'candidate.native.tm',254);C=table(R/'candidate.tm',215);states={q for q,b in T}
 mapping={q:i for i,q in enumerate(sorted(states))};mapping[254]=215
 need(mapping[0]==0 and set(C)=={(q,b)for q in range(215)for b in (0,1)},'dense state convention')
 need({(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in T.items()}==C,'all430 dense/native rows')
 cmap=read(R/'canonicalization.json')
 need({int(q):v for q,v in cmap['native_to_canonical'].items()}==mapping and cmap['native_sha256']==PINS['candidate.native.tm'] and cmap['canonical_sha256']==PINS['candidate.tm'],'recorded canonical bijection')
 sites=read(R/'sites.json');need(len(sites)==4751 and sum(op=='CD'for p,op,k in sites)==1425,'exact source count')
 need(len({p for p,op,k in sites})==4751,'unique source addresses')
 expected=[(i,pos)for i,(p,op,k)in enumerate(sites)for pos in ((False,True)if op=='CD'else(False,))]
 rep=read(R/'runtime/runtime.json');cases=read(R/'runtime/runtime_cases.json')
 need(rep['status']=='UNIVERSAL_MATHEMATICAL_PASS' and rep['proved_cases']==rep['expected_cases']==6176 and rep['site_count']==4751 and rep['working_states']==215 and rep['failures']==[],'quantified runtime result')
 need(actual['runtime']=={k:v for k,v in rep.items()if k!='blocks'},'aggregate runtime copy')
 need(rep['table_sha256']==PINS['candidate.native.tm'] and rep['sites_sha256']==PINS['sites.json'] and rep['checker_sha256']==PINS['code/runtime/symbolic_runtime.py'] and rep['helper_sha256']==PINS['code/runtime/independent_runtime.py'],'runtime exact input IDs')
 need([(c['site_index'],c['positive'])for c in cases]==expected and len(cases)==6176,'ordered complete guarded cases')
 legacy={int(q):v for q,v in read(R/'code/inputs/legacy_mapping.json').items()}
 for q in states|{254}:
  if q not in legacy:legacy[q]=q+1000
 need(len({legacy[q]for q in states|{254}})==216,'legacy mapping injective')
 L={(legacy[q],b):(w,d,legacy[z])for(q,b),(w,d,z)in T.items()};used=set()
 for c in cases:
  need(len(c['duration'])==13 and all(type(v)is int and v>=0 for v in c['duration'])and c['duration'][0]>0,'positive affine duration')
  need(len(c['motion'])==13 and all(type(v)is int for v in c['motion']),'affine motion shape')
  need(type(c['symbolic_steps'])is int and c['symbolic_steps']>0 and sum(c['kinds'].values())==c['symbolic_steps'],'event count')
  for row in c['rows']:
   need(tuple(row)in L,'case row belongs to exact remapped table');used.add(tuple(row))
 blockrows=set();blockkeys=[]
 for b in rep['blocks']:
  blockkeys.append((b['entry'],b['direction'],b['before'],b['after']))
  need(b['steps']=='v+2' and b['arbitrary_contexts']is True,'arbitrary-context block statement')
  for ev in b['trace']:
   need(ev[0]in ('literal','unary')and len(ev[1])==5,'block trace event')
   q,bit,w,d,z=ev[1];need(L[q,bit]==(w,d,z),'exact block action binding');blockrows.add((q,bit))
 need(blockkeys==[(73,1,'B','B'),(95,1,'B','C'),(48,-1,'B','B'),(112,-1,'C','B')],'four one-block schemas')
 need(used|blockrows==set(L)and len(used|blockrows)==430,'all430 literal rows covered including block rows')
 st=read(R/'runtime/startup.json');pre=read(R/'preflight.json')
 need(st==pre,'independent root preflight and runtime-startup identity')
 need(st['status']==rep['startup_status']=='CALIBRATED_DIRTY_ROOT_SEED'and st['steps']==len(st['trace'])==95714,'exact95714step root')
 need(st['state']==84 and st['head']==-8 and st['gap']==1 and st['registers']==[4,0,0,0,0,0,0,0,0] and st['spares']==[1]*40,'exact safe root tuple')
 expectedones=expected_frame();need(st['one_cells']==sorted(expectedones),'complete independent frame construction')
 # Independently replay both presentations on a truly blank sparse tape.
 # Every missing key denotes zero, so equality of the final finite support
 # establishes the entire two-way infinite tape including its zero exterior.
 blank=[]
 for name,tab,ren in [('native',T,lambda q:q),('canonical',C,lambda q:mapping[q])]:
  tape={};q=h=0;lo=hi=0
  for i,event in enumerate(st['trace']):
   bit=tape.get(h,0);need((q,bit)in tab,'no premature halt '+str(i));w,d,z=tab[q,bit]
   eq,eh,eb,ew,ed,ez=event
   need([q,h,bit,w,d,z]==[ren(eq),eh,eb,ew,ed,ren(ez)],'full stored trace replay '+str(i))
   if w:tape[h]=1
   else:tape.pop(h,None)
   q,h=z,h+d;lo=min(lo,h);hi=max(hi,h)
  need(q==ren(84)and h==-8 and set(tape)==expectedones,'whole infinite blank endpoint')
  blank.append({'presentation':name,'steps':len(st['trace']),'endpoint_state':q,'head':h,'header':57,'gap':1,'one_cells':sorted(tape),'head_range':[lo,hi],'complete_trace_matches':True,'zero_exterior':True})
 out={'status':'PASS_INDEPENDENT_215_ACTUAL_AND_BLANK_AUDIT','actual_sha256':sha(R/'actual.json'),'runtime_report_sha256':sha(R/'runtime/runtime.json'),'runtime_cases_sha256':sha(R/'runtime/runtime_cases.json'),'startup_sha256':sha(R/'runtime/startup.json'),'raw_runtime_log_sha256':sha(R/'runtime.log'),'auditor_sha256':sha(Path(__file__)),'inputs':PINS,'source_calibration':'Inherited exact210 ordinal CFG/source proof; actual root[4,0,0,0,0,0,0,0,0] satisfies its literal theorem.','runtime':{'cases':6176,'source_occurrences':4751,'decrement_sites':1425,'symbolic_rules':sum(c['symbolic_steps']for c in cases),'maximum_rules_per_case':max(c['symbolic_steps']for c in cases),'minimum_positive_duration_constant':min(c['duration'][0]for c in cases),'all_coefficients_nonnegative':True,'literal_rows_covered':430,'block_rows':len(blockrows),'root_runtime_seconds':rep['seconds'],'root_process_seconds':actual['elapsed_seconds']},'independent_blank_replays':blank,'elapsed_audit_seconds':time.monotonic()-began,'scope':'Saved full runtime/affine/row/block/input integrity audit plus two authorized independent finite blank replays from state0, checking every stored event and whole zero-exterior frame. No symbolic proof rerun or supplied code import. Ordinary induction and calibrated source proofs remain separate; no new kernel endpoint.'}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(out,indent=2)+'\n');print(out['status']);print(json.dumps(out['runtime'],indent=2))
if __name__=='__main__':main()
