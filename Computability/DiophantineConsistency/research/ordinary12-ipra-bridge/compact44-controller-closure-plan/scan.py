#!/usr/bin/env python3
"""Point-in-time controller source/provider survey; no Lean or build."""
import hashlib,json,re,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[5];BASE=ROOT/'Computability/DiophantineConsistency';R=BASE/'research/ordinary12-ipra-bridge';PLAN=BASE/'research/thirteen-model-endpoint-closure';ENDPOINT=BASE/'research/thirteen-model-endpoint-successor';AUDIT=BASE/'reviews/thirteen-model-endpoint-successor-pair-independent-audit';PARENT=Path('/tmp/ipra-thirteen-endpoint-successor-pair-01');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');BASEMAN=Path('/tmp/ipra-ordinary12-coexistence-source-03/manifest.json')
if not __debug__:raise RuntimeError('optimized Python rejected')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 need(sha(AUDIT/'CHECK.json')=='50c18ab38d6393cf784e658b5626bb6ec3cb490dc1652f5b5dcfa2b1adca1cce','endpoint audit pin')
 need(json.loads((AUDIT/'CHECK.json').read_bytes())['status']=='PASS_INDEPENDENT_THIRTEEN_ENDPOINT_SUCCESSOR_PAIR_AUDIT','endpoint audit status')
 need(sha(PLAN/'frontier-plan.json')=='73d0ff4eff130c0bf74ae7ba170e591f1b62b2d43dd0fcaf654964a4ba3e2b9e' and sha(PLAN/'source-manifest.json')=='de858182dbaab901257fe1ab0f9ede3a0a8e15f39f2b9c8b1d794f28814fc3bb' and sha(BASEMAN)=='9a7059e439bb77ab258808789fd1165cff8a4961c609e132ca0ed2130cb27ded','source manifest pins')
 plan=json.loads((PLAN/'frontier-plan.json').read_bytes());survey=json.loads((PLAN/'source-manifest.json').read_bytes());base=json.loads(BASEMAN.read_bytes());rows=dict(base['sources']);rows.update(survey['sources']);selected=plan['all_selected_source_hashes'];seed=set(plan['reusable_seeds'])
 modules={}
 for typ,mapping in [('Data',{'94517':'590069','120199':'581197','120198':'581196','60099':'290598','5394':'502425','66027':'134409','61280418874903':'172304811153038026','1365562674887717':'199319379664053821','11360754366':'342945742524'}),('Choice',{'94517':'590069','47258':'295034','120199':'581197','120198':'581196','60099':'290598'})]:
  original=BASE/'Lean/DiophantineConsistency'/('ArithmeticController'+typ+'.lean');current=R/('compact44-controller-'+typ.lower()+'-prototype')/('ArithmeticController'+typ+'Compact44.lean');old=original.read_text();new=current.read_text();mapping.update({'ArithmeticControllerData':'ArithmeticControllerDataCompact44','ArithmeticControllerChoice':'ArithmeticControllerChoiceCompact44'})
  need(sha(original)==({'Data':'1a7261dfb12d4940925149a5f078702df1b0ff7b3f5f701ff2e85a495e139f9d','Choice':'41486b89f3a8b675cd2f0a4c70d11473ac7cb0f06ee13a4967dedee1679bf62c'}[typ]) and sha(current)==({'Data':'8f28cce9e32b29bd3fd70ef193c46730aee3b2664e92037ce594ce0638c2f02c','Choice':'27d550683bcbeb285d3b84b621a2e4f61f691460ababca6c777e3214c2f9cc8e'}[typ]),'source pins '+typ)
  regex=re.compile(r'\b('+'|'.join(map(re.escape,sorted(mapping,key=len,reverse=True)))+r')\b');trans=regex.sub(lambda m:mapping[m.group()],old)
  reports=['g_mod_nat','zc_surj','zc_inj'] if typ=='Data' else ['controller_choice','rank_calibration'];appended='\n\n'+'\n'.join('#print axioms DiophantineConsistency.ArithmeticController'+typ+'Compact44.'+n for n in reports)+'\n';need(new==trans.rstrip()+appended,'exact substitution '+typ)
  imports=[v for line in new.splitlines() if line.startswith('import ') for v in line[7:].split()];modules[typ]={'source':str(current),'sha256':sha(current),'original_source_sha256':sha(original),'imports':imports,'named_reports':reports,'substitutions':mapping}
 need(modules['Data']['imports']==['DiophantineConsistency.ArithmeticStandardCasts','DiophantineConsistency.ArithmeticControllerLift','DiophantineConsistency.ArithmeticPackingBlocks','Mathlib.Tactic.ReduceModChar'] and modules['Choice']['imports']==['DiophantineConsistency.ArithmeticControllerDataCompact44','BusyBeaver.ZFC.ArithmeticCantor'],'direct imports')
 todo=modules['Data']['imports']+modules['Choice']['imports'];seen=set();external=set()
 while todo:
  n=todo.pop()
  if n=='DiophantineConsistency.ArithmeticControllerDataCompact44':continue
  if n in seen or n in external:continue
  if n not in rows:external.add(n);continue
  seen.add(n);todo.extend(rows[n]['imports'])
 need(len(seen)==23 and seen<=seed and len(external)==6,'source declared closure')
 suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash');H=sha;record=[]
 for n in sorted(seen):
  row=rows[n];src=ROOT/row['workspace_path'];need(sha(src)==row['sha256']==selected[n],'source drift '+n);per=[]
  for side in ('author','peer'):
   stem=PARENT/side/'lib'/Path(*n.split('.'));items={}
   for suffix in suffixes:
    p=Path(str(stem)+suffix);items[suffix]={'sha256':H(p),'realpath':str(p.resolve())} if p.is_file() else None
    need(not p.is_symlink() or p.is_file(),'dangling companion '+str(p))
   need(items['.olean'] is not None,'missing project object '+n)
   hist=Path('/tmp/ipra-aq29-fresh-project-pair')/side/'lib'/Path(*n.split('.'))
   for suffix in suffixes:
    actual=items[suffix];recorded=plan['direct_and_seed_output_guards'][side].get(str(hist)+suffix,'MISSING');need(recorded!='MISSING' and ((actual is None and recorded is None) or (actual is not None and recorded is not None and actual['sha256']==recorded['sha256'] and actual['realpath']==recorded['realpath'])),'historical seed guard '+n+suffix)
   per.append(items)
  need({k:(v['sha256'] if v else None) for k,v in per[0].items()}=={k:(v['sha256'] if v else None) for k,v in per[1].items()},'peer companion mismatch '+n)
  record.append({'module':n,'source_sha256':row['sha256'],'imports':row['imports'],'author':per[0],'peer':per[1]})
 ext=[]
 for n in sorted(external):
  stem=PACKAGE/Path(*n.split('.'));items={}
  for suffix in suffixes:
   p=Path(str(stem)+suffix);items[suffix]={'sha256':H(p),'realpath':str(p.resolve())} if p.is_file() else None;need(not p.is_symlink() or p.is_file(),'dangling package '+str(p))
  need(items['.olean'] is not None,'missing external object '+n)
  for side in ('author','peer'):
   r=plan['direct_external'][side].get(n);need(r is not None and r['path']==str(stem)+'.olean' and r['sha256']==items['.olean']['sha256'],'historical external pin '+n)
  ext.append({'module':n,'companions':items})
 for side in ('author','peer'):
  for typ in ('Data','Choice'):need(not (PARENT/side/'lib/DiophantineConsistency'/('ArithmeticController'+typ+'Compact44.olean')).exists(),'output collision')
 d=590069;p=581197;r=pow(2,d*(p-1),d*p*p);need(r==172304811153038026==1+d*p*502425 and (502425*134409)%p==1 and all(p%k for k in range(2,int(p**0.5)+1)),'finite arithmetic')
 print(json.dumps({'status':'PRELIMINARY_COMPACT44_CONTROLLER_SOURCE_CLOSURE_NOT_A_BUILD','modules':modules,'endpoint_audit_sha256':sha(AUDIT/'CHECK.json'),'source_declared_project_seed_modules':record,'external_direct_or_transitive_leaves':ext,'finite_arithmetic':{'residue':r,'modulus':d*p*p,'exponent':d*(p-1),'inverse':134409,'trial_division_prime':True},'scope':'Point-in-time source-declared closure and companion comparison, not simultaneous freeze, coherent paired build, package-transitive or dynamic ancestry, retained K binding or iPRA proof.'},indent=2,sort_keys=True))
if __name__=='__main__':main()
