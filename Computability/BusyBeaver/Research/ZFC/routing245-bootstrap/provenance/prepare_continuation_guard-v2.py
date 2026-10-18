#!/usr/bin/env python3
"""Bind one root-generated continuation to its actual successful predecessor.
Metadata-only adaptor: no simulation, checker, compiler, version query or build.
The generated proof guard retains the exact first-unit execution/audit tail.
"""
from pathlib import Path
import argparse,ast,difflib,hashlib,json,re
BASE=Path('/tmp/zfc-routing245-lean/bootstrap-first/check.py')
BASE_SHA='8f8b3b6c734408b5757d62004cdd93f5cd3b7f87614fca27292b1e93554c3714'
GENERATOR_SHA='72a39d8783345c01b77bbaef8ba4107cd06ad84571c989b1f0c3bef445bed1c7'
TABLE_SHA='17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
def desc(p):return dict(path=str(p),sha256=sha(p))
def replace_once(text,old,new):
 need(text.count(old)==1,'Template anchor changed: '+old[:70]);return text.replace(old,new)
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--unit',type=Path,required=True);a=ap.parse_args();B=a.unit.resolve();I=B/'source-inventory.json'
 inv=json.loads(I.read_text());index=inv['unit_index'];need(isinstance(index,int)and index>=1,'A continuation index is required.')
 module=f'BusyBeaver.ZFC.BootRouting245Chunk{index:03d}';need(inv['module']==module,'Wrong continuation module.')
 for k in ['source','audit','data','generator','canonical']:
  q=inv[k];need(sha(q['path'])==q['sha256'],'Changed generated '+k)
 need(Path(inv['source']['path']).resolve()==B/(module.rsplit('.',1)[1]+'.lean')and Path(inv['audit']['path']).resolve()==B/'Audit.lean','Unexpected generated paths.')
 need(inv['generator']['sha256']==GENERATOR_SHA and inv['canonical']['sha256']==TABLE_SHA,'Wrong generator/table.')
 need(len(inv['parents'])==1 and len(inv['metadata_inputs'])==1,'One actual predecessor/inventory required.')
 parent=inv['parents'][0];P=Path(parent['path']).resolve();need(sha(P)==parent['sha256'],'Changed predecessor record.')
 d=json.loads(P.read_text());previous=inv['metadata_inputs'][0];PI=Path(previous['path']).resolve();need(sha(PI)==previous['sha256'],'Changed predecessor inventory.')
 pi=json.loads(PI.read_text());pm='BusyBeaver.ZFC.BootRouting245First'if index==1 else f'BusyBeaver.ZFC.BootRouting245Chunk{index-1:03d}'
 need(parent['module']==pm and pi['module']==pm and pi['unit_index']==index-1,'Wrong predecessor API.')
 need(pi['endpoint']==inv['start']and pi['source']['sha256']==d['source']['sha256']and pi['audit']['sha256']==d['audit']['sha256'],'Predecessor endpoint/source binding differs.')
 need(d['status']=='PASS'and d['prepare_only']is False and d['only_standard_axioms']and d['all_input_provider_postchecks']and d['all_fresh_objects_unchanged_after_audit']and d['source_object_recorded_before_audit']and d['before']==d['after'],'Incomplete predecessor.')
 need([q['label']for q in d['commands']]==['source','audit']and all(q['exit_code']==0 for q in d['commands']),'Predecessor commands failed.')
 for p,h in d['before'].items():need(sha(p)==h,'Stale predecessor input '+p)
 f=d['fresh_modules'];need(len(f)==1 and f[0]['module']==pm,'Wrong fresh predecessor.')
 f=f[0];need(all(f[k]==d['source_pass_object'][k]for k in ['module','path','sha256','source_sha256']),'Pre-audit predecessor binding differs.')
 need(sha(f['path'])==f['sha256']==d['fresh_first_provider_before_audit']['sha256'],'Predecessor object changed.')
 for role in ['source','audit']:need(sha(d[role]['path'])==sha(d[role]['snapshot'])==d[role]['sha256'],'Predecessor snapshot changed.')
 segs=inv['segments'];need(1<=len(segs)<=4,'Require one to four blocks.');at=inv['start'];names=[]
 for q in segs:
  need(q['start']==at and isinstance(q['depth'],int)and 0<=q['depth']<=14 and q['end']==at+2**q['depth'],'Invalid contiguous segment.')
  at=q['end'];names += ['block'+str(at),'reached'+str(at)]
 need(at==inv['endpoint']and 1024<at<=407915,'Invalid endpoint.')
 if index==1:need(segs==[dict(start=1024,end=17408,depth=14)],'First continuation is the single16384 measurement.')
 if at==407915:names+=['bootstrap407915','bootstrap_active_through']
 prefix='SetTheory.BusyBeaver.ZFC.'+module.rsplit('.',1)[1]+'.';need(inv['probes']==[prefix+n for n in names]and inv['callers']==len(names)+3,'Wrong audit contract.')
 need(inv['imports']==[pm]and inv['checkpoint_name']=='checkpoint'+str(at)and inv['actual_run_theorem']=='reached'+str(at),'Wrong endpoint API.')
 need(sha(BASE)==BASE_SHA,'Frozen first guard changed.');old=BASE.read_text();text=old
 text=replace_once(text,old[old.index('"""'):old.index('"""',old.index('"""')+3)+3],f'"""Bounded exact245 actual blank-run continuation {inv["start"]} to {at}.\nExact successful predecessor, generated source/data/table pins and source-object\nbefore audit. Shared120s/-j1/-M4096/default proof limits. No builds/version query.\nRuntime framing, coverage and PA comparison remain separate.\n"""')
 vals={'MODULE':module,'PREFIX':prefix,'SOURCE_SHA':inv['source']['sha256'],'AUDIT_SHA':inv['audit']['sha256'],'PROBES':names,'PARENTS':{'previous':(str(P),sha(P),pm,d['named_axiom_probes'],d['callers'])},'CALLERS':inv['callers'],'DATA_SHA':inv['data']['sha256'],'INVENTORY_SHA':sha(I),'GENERATOR_SHA':GENERATOR_SHA}
 for k,v in vals.items():
  text,n=re.subn(r'^'+k+r'=.*$',lambda _:k+'='+repr(v),text,flags=re.M);need(n==1,'Missing constant '+k)
 text=replace_once(text,"HERE/'BootRouting245First.lean'","HERE/"+repr(module.rsplit('.',1)[1]+'.lean'))
 text=replace_once(text,"G=HERE.parent/'bootstrap-plan/generate.py'","G=Path("+repr(inv['generator']['path'])+")")
 text=replace_once(text,"assert inventory['unit_index']==0 and inventory['start']==0 and inventory['endpoint']==1024",f"assert inventory['unit_index']=={index} and inventory['start']=={inv['start']} and inventory['endpoint']=={at}")
 text=replace_once(text,"inventory['segments']==[dict(start=0,end=1024,depth=10)]","inventory['segments']=="+repr(segs))
 text=replace_once(text,"assert imports(S)==['BusyBeaver.ZFC.FastTableRouting245','BusyBeaver.ZFC.FiniteZipper']","assert imports(S)=="+repr([pm]))
 text=replace_once(text,"assert 'theorem first1024 : ZipRep (machineRouting245.run 1024) checkpoint1024' in S.read_text()",f"assert 'theorem reached{at} : ZipRep (machineRouting245.run {at}) checkpoint{at}' in S.read_text()")
 text=replace_once(text,'len(closure)==4',f'len(closure)=={4+index}')
 text=replace_once(text,'project_module_count=4',f'project_module_count={4+index}')
 text=replace_once(text,'Freeze the actual successful Fast record','Freeze the actual successful predecessor record')
 # Bind the adaptor/template and prior inventory without executing any of them.
 anchor="assert data['segments']==inventory['segments'] and data['table']['sha256']==TABLE_SHA\n"
 extra=f'''ADAPTOR=Path({str(Path(__file__).resolve())!r});TEMPLATE=Path({str(BASE)!r});PI=Path({str(PI)!r})
assert sha(ADAPTOR)=={sha(Path(__file__).resolve())!r} and sha(TEMPLATE)=={BASE_SHA!r} and sha(PI)=={sha(PI)!r}
previous_inventory=json.loads(PI.read_text())
assert previous_inventory['module']=={pm!r} and previous_inventory['endpoint']=={inv['start']}
assert previous_inventory['source']['sha256']=={d['source']['sha256']!r} and previous_inventory['audit']['sha256']=={d['audit']['sha256']!r}
'''
 text=replace_once(text,anchor,anchor+extra)
 text=replace_once(text,'S,A,D,I,G,TABLE,E0,C,ss,aa','S,A,D,I,G,TABLE,ADAPTOR,TEMPLATE,PI,E0,C,ss,aa')
 text=replace_once(text,'canonical=dict(path=str(TABLE),sha256=sha(TABLE)))','canonical=dict(path=str(TABLE),sha256=sha(TABLE)),adaptor=dict(path=str(ADAPTOR),sha256=sha(ADAPTOR)),template=dict(path=str(TEMPLATE),sha256=sha(TEMPLATE)),previous_inventory=dict(path=str(PI),sha256=sha(PI)))')
 need(text[text.index('def save():'):]==old[old.index('def save():'):],'Proof execution tail changed.');ast.parse(text)
 guard=B/'check.py';need(not guard.exists(),'Do not overwrite an existing guard.');guard.write_text(text)
 (B/'guard-from-first.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),text.splitlines(True),fromfile=str(BASE),tofile=str(guard))))
 record=dict(status='SOURCE_ONLY_GUARD_BOUND_NOT_EXECUTED',guard=desc(guard),adaptor=desc(Path(__file__).resolve()),template=desc(BASE),inventory=desc(I),parent=desc(P),project_count=4+index,probes=len(names),callers=inv['callers'],scope=f'Actual blank-run continuation {inv["start"]} to{at}; generated data remain untrusted until proof.',proof_execution=False,guard_execution=False)
 (B/'guard-binding.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
if __name__=='__main__':main()
