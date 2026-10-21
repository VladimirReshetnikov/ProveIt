#!/usr/bin/env python3
"""Independent Source160 saved-record audit. Standard library only; no supplied imports.
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
 need(st['status']=='CALIBRATED_DIRTY_ROOT_SEED' and st['steps']==len(st['trace'])==steps,'startup census')
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

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--accepted',type=Path,required=True);ap.add_argument('--literal-comparison',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();R=a.run;P=R/'packet';t0=time.monotonic();act=read(R/'actual.json')
 need(act['status']=='NINE_SELECTED_SOURCE160_LEAVES_PASS','root terminal status');need(act['before']==act['after']==read(R/'before.json')and len(act['before'])==33,'33 before/after inputs')
 for p,h in act['before'].items():need(sha(R/p)==h,'current input '+p)
 names=['reconstruct210','source210','blank-marker210','fold210','reconstruct120','source120','blank-marker120','fold120','runtime120'];need([j['name']for j in act['jobs']]==names,'ordered nine jobs')
 jobs=[]
 for j in act['jobs']:
  n=j['name'];need(j['returncode']==0 and j['timed_out']is False and 0<j['seconds']<j['cap_seconds'] and j['cap_seconds']==(360 if n=='runtime120'else90),'bounded success '+n)
  need(j['argv'][1]=='-B'and '-O'not in j['argv'],'assertions enabled');out=(R/'logs'/f'{n}.stdout').read_text();need(not(R/'logs'/f'{n}.stderr').read_bytes()and'Traceback'not in out and'NOT_PROVED'not in out,'raw log '+n)
  marker='EXACT_SOURCE_AND_TABLE_RECONSTRUCTION_PASS'if n.startswith('reconstruct')else'ALL_NATURAL_SOURCE_BISIMULATION_PASS'if n.startswith('source')else'MARKER_LEMMA_CANONICAL_ISOMORPHISM_AND_WHOLE_BLANK_PASS'if n.startswith('blank')else'INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS'if n.startswith('fold')else'UNIVERSAL_MATHEMATICAL_PASS'
  need(marker in out,'terminal raw marker '+n);jobs.append({k:j[k]for k in ('name','returncode','seconds','cap_seconds')})
 variants=[];tables={};sources={}
 for v,pre,base,steps in [('210','', 'machine/sites216.json',95714),('120','secondary','secondary/sites120.json',96284)]:
  D=P/pre;S=D/'source';M=D/'machine';B=R/('rebuilt'+v);rows=read(S/'sites215.json');sources[v]=rows
  for f in ('sites215.json','sites215.compact.json'):need((B/f).read_bytes()==(S/f).read_bytes(),'exact rebuilt source '+v+f)
  for f in ('prefold216.native.tm','k215.native.tm','k215.tm'):need((B/f).read_bytes()==(M/f).read_bytes(),'exact rebuilt table '+v+f)
  need(compact(rows)==(S/'sites215.compact.json').read_bytes()==(R/('source'+v)/'rebuilt_source215.json').read_bytes(),'compact reconstruction')
  old=read(R/'parents/K216_Permuted_Commands_2026-10-21'/base);g=cfg(rows);need(len(rows)==4751 and cfg(old)==g,'all ordinal source effects/edges')
  corr=read(R/('source'+v)/'ordinal_correspondence.json');need(corr['rows']==[[i,old[i][0],rows[i][0],*g[i]]for i in range(len(rows))],'all correspondence rows')
  sr=read(R/('source'+v)/'verification.json');need(sr['status']=='ALL_NATURAL_SOURCE_BISIMULATION_PASS'and sum(len(x[1])for x in g)==6175,'source gate');need(sr['candidate_input_sha256']==sha(S/'sites215.json')and sr['recipe_sha256']==sha(S/'dag_recipe.json')and sr['verifier_sha256']==sha(S/'verify_source.py'),'source report pins')
  need(sr['complete_guarded_CFG_sha256']==hashlib.sha256(compact(g)).hexdigest()and sr['correspondence_sha256']==sha(R/('source'+v)/'ordinal_correspondence.json'),'CFG/correspondence pins')
  T=table(M/'k215.native.tm',254);C=table(M/'k215.tm',215);cm=read(M/'canonicalization.json');m={int(k):z for k,z in cm['native_to_canonical'].items()};need(m[0]==0 and m[254]==215 and len(set(m.values()))==216,'canonical map bijection')
  need({(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in T.items()}==C and cm['native_sha256']==sha(M/'k215.native.tm')and cm['canonical_sha256']==sha(M/'k215.tm'),'all430 canonical rows');tables[v]=T
  st=json.loads(gzip.decompress((D/'evidence/startup.json.gz').read_bytes()));blank=trace_check(st,T,C,m,steps)
  if v=='120':need(st==read(R/'runtime120/startup.json'),'fresh secondary complete startup equals delivered')
  br=read(R/('blank-marker'+v+'.json'));need(br['status']=='MARKER_LEMMA_CANONICAL_ISOMORPHISM_AND_WHOLE_BLANK_PASS'and br['blank_steps']==steps and br['one_cells']==st['one_cells']and br['head']==-8 and br['native_dispatch']==84 and br['canonical_dispatch']==m[84]and br['working_states']==br['graph_reachable_working_states']==215 and br['rows']==430,'blank marker gate')
  f=read(R/('fold'+v+'.json'));need(f['status']=='INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS'and(f['old_states'],f['new_states'],f['keep'],f['drop'],f['radius'],f['fuel'])==(216,215,164,183,5,97),'fold gate')
  need(f['old_sha256']==sha(M/'prefold216.native.tm')and f['new_sha256']==sha(M/'k215.native.tm')and f['checker_sha256']==sha(P/'code/check_joint_fold.py'),'fold exact identities')
  need(f['changed_old_rows']==[[164,0],[183,0]]and f['nontrivial_contexts']==128 and f['positive_old_new_block_histogram']==[[1,1,f['inductive_window_contexts']-128],[1,3,128]]and f['negative_control']['status']=='REJECTED','positive block census and control')
  variants.append({'variant':v,'source_occurrences':4751,'guarded_successors':6175,'all_source_effects_and_edges_equal':True,'five_rebuilt_files_byte_equal':True,'native_sha256':sha(M/'k215.native.tm'),'source_compact_sha256':sha(S/'sites215.compact.json'),'fold_contexts':f['inductive_window_contexts'],'blank':blank})
 # Primary actuals are transferred; verify the supplied bijection directly.
 lc=read(a.literal_comparison);need(lc['status']=='EXACT_LITERAL_ISOMORPHISM_SOURCE_AND_DELIVERED_RECORD_TRANSFER_PASS','literal transfer status');p=next(x for x in lc['sources']if x['source']==160);m={int(k):v for k,v in p['native_state_map'].items()};AT=table(a.accepted/'k215.native.tm',254)
 need(sha(a.accepted/'k215.native.tm')==lc['accepted_native_sha256']and m[0]==0 and m[84]==84 and m[254]==254 and len(set(m.values()))==216,'accepted map binding')
 need({(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in AT.items()}==tables['210'],'primary all430 actual transfer')
 need(read(a.accepted/'sites215.json')==sources['210'],'primary exact accepted source')
 rep=read(R/'runtime120/runtime.json');cases=read(R/'runtime120/runtime_cases.json');D=P/'secondary';need(rep==act['runtime120'],'aggregate full runtime copy')
 need(rep['status']=='UNIVERSAL_MATHEMATICAL_PASS'and rep['proved_cases']==rep['expected_cases']==len(cases)==6176 and rep['site_count']==4751 and rep['working_states']==215 and rep['failures']==[],'runtime gate')
 for k,p in [('table_sha256',D/'machine/k215.native.tm'),('sites_sha256',D/'source/sites215.json'),('checker_sha256',P/'code/runtime/symbolic_runtime.py'),('helper_sha256',P/'code/runtime/independent_runtime.py')]:need(rep[k]==sha(p),'runtime binding '+k)
 expected=[(i,pos)for i,(p,op,k)in enumerate(sources['120'])for pos in ((False,True)if op=='CD'else(False,))];need([(c['site_index'],c['positive'])for c in cases]==expected,'6176 ordered guards')
 legacy={int(q):z for q,z in read(P/'code/inputs/legacy_mapping.json').items()};T=tables['120'];states={q for q,b in T}|{254}
 for q in states:legacy.setdefault(q,q+1000)
 need(len({legacy[q]for q in states})==216,'legacy injection');L={(legacy[q],b):(w,d,legacy[z])for(q,b),(w,d,z)in T.items()};used=set()
 for c in cases:
  need(len(c['duration'])==13 and all(type(v)is int and v>=0 for v in c['duration'])and c['duration'][0]>0,'positive affine duration')
  need(len(c['motion'])==13 and all(type(v)is int for v in c['motion']),'affine motion');need(c['symbolic_steps']==sum(c['kinds'].values())and c['symbolic_steps']>0,'rule counts')
  for row in c['rows']:need(tuple(row)in L,'case table row');used.add(tuple(row))
 blockrows=set();keys=[]
 for b in rep['blocks']:
  keys.append((b['entry'],b['direction'],b['before'],b['after']));need(b['steps']=='v+2'and b['arbitrary_contexts']is True,'arbitrary context block')
  for e in b['trace']:
   need(e[0]in ('literal','unary'),'block event');q,bit,w,d,z=e[1];need(L[q,bit]==(w,d,z),'block actual action');blockrows.add((q,bit))
 need(keys==[(73,1,'B','B'),(95,1,'B','C'),(48,-1,'B','B'),(112,-1,'C','B')],'four exact block schemas');need(used|blockrows==set(L)and len(L)==430,'all430 rows covered')
 rules=sum(c['symbolic_steps']for c in cases);minclock=min(c['duration'][0]for c in cases);need((rules,minclock)==(1698845,9),'runtime rules/minimum')
 out={'status':'PASS_INDEPENDENT_SOURCE160_SAVED_ACTUAL_AUDIT','actual_sha256':sha(R/'actual.json'),'auditor_sha256':sha(Path(__file__)),'input_count':33,'all_inputs_unchanged':True,'jobs':jobs,'variants':variants,'primary_transfer':{'literal_comparison_sha256':sha(a.literal_comparison),'all430_rows_independently_match':True,'source_equal':True,'fresh_primary_runtime':False},'secondary_runtime':{'cases':6176,'rules':rules,'minimum_duration':minclock,'rows_including_blocks':430,'block_rows':len(blockrows),'process_seconds':act['jobs'][-1]['seconds'],'report_seconds':rep['seconds'],'runtime_cases_sha256':sha(R/'runtime120/runtime_cases.json')},'seconds':time.monotonic()-t0,'scope':'Independent saved evidence audit with all recorded blank events bound to native/canonical tables and full zero-exterior endpoint; own interval CFG reconstruction and literal transfer-map check. No supplied code import/execution, no runtime rerun, no fresh proof of symbolic rules/fold induction, no kernel claim. Full manuscript and supplied execution-closure review remain attributed to root.'}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(out,indent=2)+'\n');print(out['status']);print(json.dumps(out['secondary_runtime'],indent=2))
if __name__=='__main__':main()
