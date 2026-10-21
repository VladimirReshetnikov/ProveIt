#!/usr/bin/env python3
"""Root independent Source162 saved-record audit. Standard library only; no supplied imports.
Validates recorded events, not a new machine or symbolic-checker invocation.
"""
import argparse,gzip,hashlib,json,time
from pathlib import Path

def need(p,m):
 if not p:raise ValueError(m)
def read(p):return json.loads(p.read_bytes())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def compact(x):return (json.dumps(x,separators=(',',':'))+'\n').encode()
def table(p,halt,count=215):
 t={}
 for line in p.read_text().splitlines():
  if not line.strip() or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));need((q,b)not in t and b in (0,1) and w in (0,1) and d in ('L','R'),'table syntax');t[q,b]=(w,1 if d=='R' else -1,z)
 s={q for q,b in t};need(len(s)==count and set(t)=={(q,b)for q in s for b in (0,1)},'total state census')
 need(0 in s and {z for w,d,z in t.values()}-s=={halt},'initial/halt states');return t

def cfg(rows):
 paths=[p for p,op,k in rows];need(len(paths)==len(set(paths)) and paths==sorted(paths),'unique ordered leaves')
 spans={}
 for i,p in enumerate(paths):
  for n in range(len(p)+1):
   x=p[:n]
   if x not in spans:spans[x]=[i,i+1]
   else:spans[x][1]=i+1
 leaves=set(paths)
 for p in spans:
  need((p+'0'not in spans and p+'1'not in spans)if p in leaves else(p+'0'in spans and p+'1'in spans),'full prefix tree')
 def jump(p,bit,n):
  for i in range(len(p)-1,-1,-1):
   if p[i]==bit:
    n-=1
    if n==0:return spans[p[:i]][1 if bit=='0' else 0]%len(rows)
  return 0
 out=[]
 for i,(p,op,k)in enumerate(rows):
  need(op in ('CI','CD','CB','CC','CH'),'opcode');n=(i+1)%len(rows)
  if op in ('CI','CD'):need(type(k)is int and 0<=k<9,'register')
  if op in ('CB','CC'):need(type(k)is int and k>0,'control count')
  e=['increment',k]if op=='CI'else ['decrement',k]if op=='CD'else['halt']if op=='CH'else['identity']
  targets=[n]if op=='CI'else[jump(p,'0',1),n]if op=='CD'else[jump(p,'0',k)]if op=='CB'else[jump(p,'1',k)]if op=='CC'else[]
  out.append([e,targets])
 return out

def frame():
 logical=[4,0,0,0,0,0,0,0,0];physical=[0]*9
 for i,j in enumerate((6,2,0,4,3,7,8,5,1)):physical[j]=logical[i]
 ones={-9,57};pos=58
 for v in physical+[1]*40:ones.update(range(pos+1,pos+v+2));pos+=v+2
 return ones

def trace_check(st,T,C,m,steps):
 need(st['status']=='SAFE_SOURCE_ROOT' and st['steps']==len(st['trace'])==steps,'startup census')
 need((st['state'],st['head'],st['gap'])==(84,-8,1)and st['registers']==[4,0,0,0,0,0,0,0,0]and st['spares']==[1]*40,'calibrated root tuple')
 support=set();q=h=0;lo=hi=0
 # Each supplied event determines the update; both tables are checked against
 # that event, so this only audits the stored finite witness.
 for event in st['trace']:
  eq,eh,b,w,d,z=event;need((eq,eh)==(q,h)and b==int(h in support),'stored trace continuity/read')
  need(T[q,b]==(w,d,z)and C[m[q],b]==(w,d,m[z]),'stored event native/dense actions')
  if w:support.add(h)
  else:support.discard(h)
  q,h=z,h+d;lo=min(lo,h);hi=max(hi,h)
 need((q,h)==(84,-8)and sorted(support)==st['one_cells']==sorted(frame()),'whole frame and zero exterior')
 return {'stored_events':steps,'native_state':84,'canonical_state':m[84],'head':h,'gap':1,'header':57,'logical_registers':st['registers'],'spares':40,'one_cells':len(support),'head_range':[lo,hi],'all_events_bound_to_both_tables':True,'zero_exterior':True}

def gz(p):return json.loads(gzip.decompress(p.read_bytes()))

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--source164',type=Path,required=True);ap.add_argument('--comparison',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();R=a.run;P=R/'inputs/packet';O=R/'results';act=read(R/'actual.json');t0=time.monotonic()
 need(act['status']=='SEVEN_SELECTED_SOURCE162_LEAVES_PASS'and act['assertions_enabled'],'terminal/assertion gate')
 need(act['before']==act['after']==act['copied_after']and len(act['before'])==26,'26 inputs unchanged')
 for rel,h in act['before'].items():need(sha(R/'inputs'/rel)==h,'input '+rel)
 names=['reconstruct','decoder','blank','restricted_matrices','rejected_CB1','full_runtime','saved_interface']
 need([j['name']for j in act['jobs']]==names,'seven ordered jobs')
 for j in act['jobs']:
  need(j['returncode']==0 and not j['timed_out']and 0<j['seconds']<j['timeout_seconds'],'process '+j['name'])
  need(j['argv'][1]=='-B'and'-O'not in j['argv'],'assertions enabled')
  for key in('stdout','stderr'):need(sha(R/j[key]['path'])==j[key]['sha256'],'raw log identity')
  need(not(R/j['stderr']['path']).read_bytes(),'empty stderr')
 for rel,r in act['outputs'].items():need(sha(O/rel)==r['sha256']and(O/rel).stat().st_size==r['size'],'output '+rel)
 for r in act['fresh_saved_byte_matches']:
  need((O/r['fresh']).read_bytes()==(P/r['saved']).read_bytes()and sha(O/r['fresh'])==r['sha256'],'six exact artifacts')
 need(len(act['fresh_saved_byte_matches'])==6,'six artifacts')
 rows=read(P/'source/sites215.json');g=cfg(rows);need(len(rows)==4751 and sum(len(x[1])for x in g)==6175,'complete source graph')
 need(cfg(read(R/'inputs/parents/reference_source/sites216.json'))==g,'permuted source bisimulation')
 need(sha(P/'source/sites215.json')=='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba','exact accepted source')
 T=table(P/'machine/k215.native.tm',254);C=table(P/'machine/k215.tm',215);cm=read(P/'machine/canonicalization.json');m={int(q):z for q,z in cm['native_to_canonical'].items()}
 need(len(m)==len(set(m.values()))==216 and(m[0],m[84],m[254])==(0,83,215),'canonical bijection')
 need({(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in T.items()}==C,'430 native/dense rows')
 st=gz(O/'runtime/startup.json.gz');blank=trace_check(st,T,C,m,95726)
 br=read(O/'blank.json');need(br['status']=='INDEPENDENT_K215_TABLE_AND_BLANK_PASS'and br['whole_tape_one_cells']==st['one_cells']and br['startup_steps']==95726,'separate blank record')
 decoder=read(O/'decoder.json');need(decoder['status']=='EXACT_K215_ALL_PREFIX_BINDINGS_PASS'and decoder['compound_occurrences']==4750 and decoder['candidate_native_sha256']==sha(P/'machine/k215.native.tm'),'decoder gate')
 reconstruction=read(O/'rebuild/reconstruction.json');need(reconstruction['status']=='EXACT_K215_CONSTRUCTION_AND_SOURCE_BISIMULATION_PASS'and reconstruction['deleted_states']==[224]and reconstruction['changed_retained_rows']==35,'reconstruction gate')
 rep=read(O/'runtime/runtime.json');saved=read(P/'evidence/runtime.json');need({k:v for k,v in rep.items()if k!='seconds'}=={k:v for k,v in saved.items()if k!='seconds'},'runtime report except timing')
 need(rep['status']=='UNIVERSAL_MATHEMATICAL_PASS'and rep['proved_cases']==rep['expected_cases']==6176 and rep['working_states']==215 and rep['transition_rows']==430,'runtime gate')
 for key,path in [('table_sha256','machine/k215.native.tm'),('source_sha256','source/sites215.json'),('checker_sha256','code/runtime/symbolic_runtime.py'),('helper_sha256','code/runtime/independent_runtime.py'),('wrapper_sha256','code/validate_runtime.py')]:need(rep[key]==sha(P/path),'runtime pin '+key)
 cases=gz(O/'runtime/runtime_cases.json.gz');need(rep['case_receipts_sha256']==sha(O/'runtime/runtime_cases.json.gz'),'case binding')
 expected=[(i,b)for i,(_,op,_)in enumerate(rows)for b in((False,True)if op=='CD'else(False,))];need([(c['site_index'],c['positive'])for c in cases]==expected,'ordered exhaustive guards')
 legacy={int(q):z for q,z in read(P/'code/inputs/legacy_mapping.json').items()};states={q for q,b in T}|{254}
 for q in states:legacy.setdefault(q,q+1000)
 need(len({legacy[q]for q in states})==216,'legacy injection');L={(legacy[q],b):(w,d,legacy[z])for(q,b),(w,d,z)in T.items()};used=set()
 for c in cases:
  need(len(c['duration'])==13 and all(type(v)is int and v>=0 for v in c['duration'])and c['duration'][0]>0,'positive affine duration')
  need(len(c['motion'])==13 and all(type(v)is int for v in c['motion']),'affine motion')
  need(c['symbolic_steps']==sum(c['kinds'].values())and c['symbolic_steps']>0,'rule counts')
  for row in c['rows']:need(tuple(row)in L,'literal row reference');used.add(tuple(row))
 blockrows=set();keys=[]
 for b in rep['blocks']:
  keys.append((b['entry'],b['direction'],b['before'],b['after']));need(b['steps']=='v+2'and b['arbitrary_contexts']is True,'block scope')
  for e in b['trace']:
   need(e[0]in('literal','unary'),'block event');q,bit,w,d,z=e[1];need(L[q,bit]==(w,d,z),'block exact action');blockrows.add((q,bit))
 need(keys==[(73,1,'B','B'),(95,1,'B','C'),(48,-1,'B','B'),(112,-1,'C','B')],'four block schemas')
 need(used|blockrows==set(L),'all430 rows');rules=sum(c['symbolic_steps']for c in cases);clock=min(c['duration'][0]for c in cases);need((rules,clock)==(1698790,6),'rules/minimum')
 mat=read(O/'countermodels.json');need(mat['status']=='FOUR_EXACT_IMPLICATIONAL_COUNTERMODELS_PASS'and sum(x['axiom_assignments']for x in mat['checked'])==108,'matrix gate')
 neg=read(R/'logs/rejected_CB1.stdout');need(neg['status']=='CONCRETE_REJECTED_SHORTCUT_COUNTEREXAMPLE'and neg['rejected_table_actual']['steps']==44 and neg['corrected_table_actual']['steps']==156,'negative control')
 need(neg['rejected_table_actual']['one_cells']!=neg['expected_one_cells']==neg['corrected_table_actual']['one_cells'],'whole-frame defect/control')
 other=a.source164/'candidate215';cmp=read(a.comparison);n={int(q):z for q,z in cmp['source162_to164']['mapping'].items()};TT=table(other/'k215.native.tm',254)
 need(len(n)==len(set(n.values()))==216 and(n[0],n[84],n[254])==(0,84,254),'164 transfer bijection')
 need({(n[q],b):(w,d,n[z])for(q,b),(w,d,z)in T.items()}==TT and read(other/'sites215.json')==rows,'164 all430/source transfer')
 summary={'status':'PASS_ROOT_INDEPENDENT_SOURCE162_ACTUAL_AND164_TRANSFER','actual_sha256':sha(R/'actual.json'),'auditor_sha256':sha(Path(__file__)),'inputs':26,'inputs_unchanged':True,'selected_jobs':7,'all_source_effects_and6175_edges_checked':True,'canonical_rows':430,'cases':6176,'symbolic_rules':rules,'minimum_duration':clock,'covered_rows':430,'block_rows':len(blockrows),'blank':blank,'source164_transfer':{'source_equal':True,'all430_rows':True,'native_sha256':sha(other/'k215.native.tm'),'fresh_full_runtime':False},'seconds':time.monotonic()-t0,'scope':'Root saved-output audit; no supplied imports or candidate/checker execution. Every stored blank event and complete support checked in native/dense tables, all case guards/counts/rows/durations and direct164 conjugacy checked. Original ordinary proofs and symbolic-rule soundness remain separately reviewed premises.'}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(summary,indent=2)+'\n');print(summary['status'])
if __name__=='__main__':main()

