#!/usr/bin/env python3
"""Bounded inert-data endpoint splice; no archived code execution or full-stream claim."""
import argparse, collections, hashlib, io, json, pathlib, subprocess, zipfile
REV='c5612efa171fa62470285049ee45d1d06ee25578'
PINS={'44': {'path': 'docs/incoming/Complete_Positive_Certificate_for_the_Literal_Periodic_Ant_Package.zip', 'sha256': '3025a1efd5947e624a23f90a07dea7a826410d25944c3c968ea45edfd71013eb', 'size': 767662, 'git_blob': '10a53813867e7c7868b1bb88a0b621d5ffc2a822', 'members': {'report44-recovered/certificate/data/endpoint_folded_fixed_numerals_source.json': 'dd5a29f925e896bff6759508b4d61c6bee65a18f9e0754d73610f1a0b783d01d', 'report44-recovered/certificate/merged_source.py': 'eafe92d6e57782347f430a4f1d6ea5693bd6a48300d2db0294b3ab7026b96395', 'report44-recovered/certificate/one-input-receipt.json': 'c8a933b8844414c8240777d2fbf1cc34631be4a7686f1e670c2d0753c549853f', 'report44-recovered/certificate/two-input-receipt.json': 'a878dd9894b50143aed138ac5aa255fae95231041026c2895fc930cad447d3fb'}}, '48': {'path': 'docs/incoming/Exact_Fusion_of_the_Ant_Background_Polynomials_Package.zip', 'sha256': '45f8dcf697012fc67cd9155f76980787fef8ff3cb4f4746ef54c4c3375c7bb65', 'size': 2162628, 'git_blob': '5c17a62cb5519c85608b9c6a50184e2d95347bc4', 'members': {'Research_Report48/science/PROOF.md': '0a140e526a8c7e7ee5076204e258fdddd431d8c02e49dd9a8eff9a673d195af8', 'Research_Report48/science/fused-receipt.json': '8230ba6bed0e6209f814094168551282252c709681cc0b744cace678e4b703ee', 'Research_Report48/science/fusion_source.py': '5e433001dcdb4a26f7dcb0419a41f124fae983aeb76088d55d4b603802232f60', 'Research_Report48/science/owned_report44/data/endpoint_folded_fixed_numerals_source.json': 'dd5a29f925e896bff6759508b4d61c6bee65a18f9e0754d73610f1a0b783d01d', 'Research_Report48/science/owned_report44/merged_source.py': 'eafe92d6e57782347f430a4f1d6ea5693bd6a48300d2db0294b3ab7026b96395'}}}
PORTS=['W','K','C','D','HxPlus','HyPlus','BoundCol','FinalHead','FinalSignPlus']
DEAD=['WSquare_'+str(i) for i in range(15,20)]+['VPowerBuild_'+str(i)for i in range(1,5)]
def need(ok,msg):
 if not ok: raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def pairs(ps):
 d={}
 for k,v in ps:
  need(k not in d,'duplicate JSON key');d[k]=v
 return d
def read(b):return json.loads(b,object_pairs_hook=pairs)
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=True)
def blobs(repo):
 answer={}
 for a in PINS.values():
  spec=REV+':'+a['path'];b=subprocess.check_output(['git','-C',str(repo),'show',spec])
  need(len(b)==a['size'] and sha(b)==a['sha256'],'archive bytes')
  need(subprocess.check_output(['git','-C',str(repo),'rev-parse',spec]).decode().strip()==a['git_blob'],'Git blob')
  z=zipfile.ZipFile(io.BytesIO(b));need(len(z.namelist())==len(set(z.namelist())),'duplicate ZIP member')
  for name,digest in a['members'].items():
   data=z.read(name);need(sha(data)==digest,'member '+name);answer[name]=data
 return answer
ZERO=(0,)*len(PORTS)
def constant(c):return {ZERO:c}if c else{}
def add(a,b,sign=1):
 d=a.copy()
 for m,c in b.items():d[m]=d.get(m,0)+sign*c
 return {m:c for m,c in d.items()if c}
def mul(a,b):
 d={}
 for m,c in a.items():
  for n,e in b.items():
   key=tuple(x+y for x,y in zip(m,n));d[key]=d.get(key,0)+c*e
 return {m:c for m,c in d.items()if c}
def initial():return {s:{tuple(int(i==j)for i in range(len(PORTS))):1}for j,s in enumerate(PORTS)}|{'1':constant(1)}
def interpret(rows,outputs):
 values=initial();counts=collections.Counter();seen=set(values)
 for name,op,a,b in rows:
  need(name not in seen and a in seen and b in seen and op in ['+','-','*'],'DAG closure')
  aa,bb=values[a],values[b];values[name]=mul(aa,bb)if op=='*'else add(aa,bb,1 if op=='+'else-1)
  seen.add(name);counts[op]+=1
 residuals=[add(values[a],values[b],-1)for a,b in outputs]
 live={a for pair in outputs for a in pair}
 for name,op,a,b in reversed(rows):
  if name in live:live.update((a,b))
 return values,residuals,dict(counts),[name for name,_,_,_ in rows if name in live]
def gchain():
 rows=[];v='W'
 for bit in bin(576000)[3:]:
  name='InitG_'+str(len(rows));rows.append([name,'*',v,v]);v=name
  if bit=='1':
   name='InitG_'+str(len(rows));rows.append([name,'*',v,'W']);v=name
 return rows,v
def verify(repo):
 b=blobs(repo);ep=read(b['report44-recovered/certificate/data/endpoint_folded_fixed_numerals_source.json'])
 need(b['Research_Report48/science/owned_report44/data/endpoint_folded_fixed_numerals_source.json']==b['report44-recovered/certificate/data/endpoint_folded_fixed_numerals_source.json'],'same endpoint')
 need(b['Research_Report48/science/owned_report44/merged_source.py']==b['report44-recovered/certificate/merged_source.py'],'same main grammar')
 old=[[r['out'],{'add':'+','sub':'-','mul':'*'}[r['op']],*r['args']]for r in ep['gates']]
 need(len(old)==42 and ep['power_targets']=={'K':'K','ThreeToU':None,'T':'TBuild_9','WToV':'VPowerBuild_4'},'endpoint interface')
 prefix,G=gchain();need(len(prefix)==23,'paid G chain')
 new=[]
 for name,op,a,c in old:
  if name in DEAD:continue
  new.append([name,op,G if a=='VPowerBuild_4'else a,G if c=='VPowerBuild_4'else c])
 need(len(new)==33 and [r[0]for r in old if r[0]not in {x[0]for x in new}]==DEAD,'deleted exactly9')
 v0,r0,c0,l0=interpret(prefix+old,ep['equalities']);v1,r1,c1,l1=interpret(prefix+new,ep['equalities'])
 need(r0==r1,'three complete residual identities')
 need(v0[G]==v0['VPowerBuild_4'],'paid G matches endpoint')
 need(len(l1)==56 and len(l0)==42,'local liveness')
 for name,_,_,_ in new:need(v0[name]==v1[name],'preserved register '+name)
 sos0={};sos1={}
 for p,q in zip(r0,r1):sos0=add(sos0,mul(p,p));sos1=add(sos1,mul(q,q))
 need(sos0==sos1,'local SOS')
 r48=read(b['Research_Report48/science/fused-receipt.json']);models={}
 for arity in [2,1]:
  old44=read(b['report44-recovered/certificate/'+('two'if arity==2 else'one')+'-input-receipt.json'])
  join=r48['joins'][str(arity)];pre=r48['prefix'];fusion=join['fusion']['stages'];fm=sum(x['M']for x in fusion.values());fa=sum(x['A']for x in fusion.values())
  need((fm,fa)==(46159,45948),'fused spatial ledger')
  need(join['old_main_source_sha256']==old44['source_sha256'],'main stream inheritance')
  need(join['removed_dense_horner_gates']==2303996 and join['all_other_main_records_preserved']is True,'splice scope')
  need(join['retained_old_main_gates']+2303996==old44['single_polynomial']['total'],'whole counted main')
  # Each old dense Horner interval has equally many M/A operations.
  rm=old44['single_polynomial']['M']-1151998;ra=old44['single_polynomial']['A']-1151998
  need(pre['M']+fm+rm==join['M'] and pre['A']+fa+ra==join['A'],'inherited M/A sum')
  begin=pre['total']+fm+fa+old44['components']['endpoint']['source_interval'][0]-2303996
  models[str(arity)]={'strict_prefix_unchanged':pre,'fused_spatial_unchanged':{'M':fm,'A':fa,'total':fm+fa},'retained_main_after_splice':{'M':rm-9,'A':ra,'total':rm+ra-9},'full_grammar_count_inherited_plus_verified_delta':{'M':join['M']-9,'A':join['A'],'total':join['total']-9},'prescribed_coefficient_Report44_count_after_same_splice':{'M':old44['single_polynomial']['M']-9,'A':old44['single_polynomial']['A'],'total':old44['single_polynomial']['total']-9},'positive_witnesses_unchanged':join['positive_witnesses'],'residuals_unchanged':join['residual_metadata_records'],'final_equations':1,'exact_degree_inherited':2304000,'old_fused_endpoint_interval':[begin,begin+42],'new_fused_endpoint_interval':[begin,begin+33],'paid_G_fused_register':pre['total']+199,'parent_full_stream_sha256':join['source_sha256'],'new_full_stream_sha256':None}
 return {'status':'PASS_LOCAL_EXACT_SPLICE_WITH_INHERITED_FULL_GRAMMAR_COUNTS','source_sha256':sha(pathlib.Path(__file__).read_bytes()),'arrival_revision':REV,'pins':PINS,'execution_scope':'Only this new stdlib checker executes; archives are inert data. The 14.6-million-row source is not regenerated; its compact grammar and ledger are inherited.','ports':PORTS,'positive_witnesses_unchanged':ep['new_positive_witnesses'],'paid_initializer_G_chain':prefix,'G_output':G,'parent_endpoint_rows':old,'new_endpoint_rows':new,'equalities':ep['equalities'],'deleted_rows':DEAD,'counts':{'old_endpoint':{'M':37,'A':5,'total':42},'new_endpoint':{'M':28,'A':5,'total':33},'new_local_rows_including_already_paid_G':56,'all_new_local_rows_live':True},'identities':{'preserved_endpoint_registers':33,'complete_residuals':3,'residual_coefficient_entries':sum(len(p)for p in r0),'local_SOS_coefficient_entries':len(sos0),'ring':'Z[W,K,C,D,HxPlus,HyPlus,BoundCol,FinalHead,FinalSignPlus]'},'whole_source_specification':{'parent':'Report48 pinned complete grammar for selected arity','edit':'Replace its unchanged Report44 endpoint42 block by new_endpoint_rows, bind InitG output to existing old main register199, translate every later register reference by deletion map; preserve all declarations/residuals/full SOS.','full_stream_emitted':False,'global_liveness_recount_claimed':False,'fixed_prefix_dead_or_unused_rows':'Retained as charged by parent; only the nine specified private endpoint rows are omitted.'},'models':models}
def main():
 p=argparse.ArgumentParser();p.add_argument('--repo-root',type=pathlib.Path,required=True);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=pathlib.Path);g.add_argument('--expect',type=pathlib.Path);a=p.parse_args();out=verify(a.repo_root)
 if a.expect:need(canonical(read(a.expect.read_bytes()))==canonical(out),'receipt differs')
 else:
  with a.output.open('x')as f:json.dump(out,f,indent=2);f.write('\n')
 print(out['status'])
if __name__=='__main__':main()
