#!/usr/bin/env python3
"""Independent provenance binding and isolated standard-library constructions."""
from pathlib import Path
from zipfile import ZipFile
import json,os,shutil,subprocess,sys,tempfile
from independent_facts import read,sha,dump,table,encode,serialize_tree,interval_cfg,arithmetic_cfg,TABLE,SOURCE,NATIVE
ROOT=Path(__file__).resolve().parents[2];OUT=Path(__file__).resolve().parent
C=ROOT/'research_sub218/construction';S=ROOT/'research_sub219/grammar/source_proof_218';B=ROOT/'research_sub219/intake/K219_Construction_2026-10-20';candidate=ROOT/'research_sub219/decoder/reuse12_focused_bfs/candidate_4dd4ca3893a80b99'

def main():
 temporary=Path(tempfile.mkdtemp(prefix='k218-independent-provenance-'));line=temporary/'lineage';src=temporary/'source';line.mkdir();src.mkdir()
 inputs={}
 for name in('build_lineage.py','lineage_recipe.json','source_equivalence.py','build218.py','basis/direct188.tm','basis/direct188.sites.json','upstream_basis/upstream219.native.tm','upstream_basis/upstream219.sites.json'):
  target=line/name;target.parent.mkdir(exist_ok=True,parents=True);shutil.copy2(C/name,target);inputs['construction/'+name]=sha(target)
 for name in('reconstruct_source.py','baseline_sites219.json','dag_recipe.json','candidate_sites218.json'):
  shutil.copy2(S/name,src/name);inputs['source_proof/'+name]=sha(src/name)
 env={'PATH':os.environ['PATH'],'PYTHONPATH':'','PYTHONNOUSERSITE':'1','PYTHONDONTWRITEBYTECODE':'1','HOME':str(temporary),'LC_ALL':'C.UTF-8'}
 commands=[[sys.executable,str(line/'build_lineage.py'),'--out',str(line/'output')],[sys.executable,str(src/'reconstruct_source.py')]]
 for number,command in enumerate(commands):
  proc=subprocess.run(command,cwd=temporary,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True);(OUT/f'isolated_construction_{number}.log').write_text(proc.stdout);assert proc.returncode==0,proc.stdout
 built=line/'output'
 assert (built/'candidate.tm').read_bytes()==(candidate/'candidate.tm').read_bytes()and sha(built/'candidate.tm')==TABLE
 assert (built/'candidate.native.tm').read_bytes()==(candidate/'candidate.native.tm').read_bytes()and sha(built/'candidate.native.tm')==NATIVE
 assert (built/'candidate.sites.json').read_bytes()==(candidate/'sites.json').read_bytes()==(src/'reconstructed_sites218.json').read_bytes()and sha(built/'candidate.sites.json')==SOURCE
 assert (built/'lineage.json').read_bytes()==(C/'lineage_rebuilt/lineage.json').read_bytes()
 for name in('verification.json','ordinal_correspondence.json'):assert(src/name).read_bytes()==(S/name).read_bytes()
 # Independently apply the declarative allocation edits, not the constructor.
 raw=table(B/'machine/k219.native.tm');rename={301:102,302:120};t={(rename.get(q,q),b):(w,d,rename.get(z,z))for(q,b),(w,d,z)in raw.items()};recipe=read(C/'lineage_recipe.json');s=read(B/'machine/sites219.json');reference=interval_cfg(s);initial=s
 checks=[]
 for stage in recipe['allocation_stages']:
  name=stage['name']
  if name in recipe['source_grammars']:
   grammar=recipe['source_grammars'][name];built_nodes=[]
   for n in grammar['nodes']:
    built_nodes.append(tuple(n)if isinstance(n[0],str)else(built_nodes[n[0]],built_nodes[n[1]]))
   assert len(set(built_nodes))==len(built_nodes);s=serialize_tree(built_nodes[grammar['root']])
  assert s==read(built/(name+'.sites.json'))and s[:37]==initial[:37]
  assert [v[1:]for v in s]==[v[1:]for v in initial]and interval_cfg(s)==arithmetic_cfg(s)==reference
  for q,b,old,new in stage['edits']:
   conv=lambda v:None if v is None else(v[0],1 if v[1]=='R'else -1,v[2])
   assert t.get((q,b))==conv(old)
   if new is None:del t[q,b]
   else:t[q,b]=conv(new)
  assert encode(t)==(built/(name+'.tm')).read_bytes()and sha(built/(name+'.tm'))==stage['table_sha256']
  checks.append(dict(stage=name,explicit_edits=len(stage['edits']),table_sha256=stage['table_sha256'],source_sha256=stage['source_sha256'],states=stage['states']))
 assert encode(t)==(C/'basis/direct188.tm').read_bytes()
 # Accepted baseline source/table are actual members of the pinned original archive.
 archive=ROOT/'research_sub219/intake/K219_Construction_2026-10-20.zip';assert sha(archive)=='04813567f393b6c4015a96aba092159e9021703b4b662c7be69bd2a86497e31b'
 with ZipFile(archive)as z:
  assert z.testzip()is None
  for file in('machine/k219.native.tm','machine/sites219.json'):assert z.read('K219_Construction_2026-10-20/'+file)==(B/file).read_bytes()
 # Seed certificates are historical binding, not substitutes for fresh218 proof.
 certified=[]
 for name,stage in [('startup37_audit','startup37'),('direct188_audit','direct188')]:
  d=ROOT/'research_sub219'/name;cert=read(d/'complete_certificate.json')
  assert cert['table_sha256']==sha(built/(stage+'.tm'))and cert['source_sha256']==sha(built/(stage+'.sites.json'))
  for file,h in cert['hashes'].items():assert sha(d/file)==h,(name,file)
  certified.append(dict(stage=stage,certificate_sha256=sha(d/'complete_certificate.json'),table_sha256=cert['table_sha256'],source_sha256=cert['source_sha256']))
 # Every important fresh receipt uses the same final bytes, not merely matching names.
 facts=read(OUT/'independent_facts.json');run=read(OUT/'runtime_evidence_audit.json');lineage=read(built/'lineage.json');source=read(src/'verification.json')
 assert facts['table_sha256']==run['table_sha256']==lineage['pinned_inputs']['final_table']==TABLE
 assert facts['source_sha256']==run['source_sha256']==lineage['pinned_inputs']['final_source']==source['candidate_source_sha256']==SOURCE
 assert facts['native_sha256']==lineage['native_sha256']==NATIVE
 result=dict(status='INDEPENDENT_K218_PROVENANCE_AND_ISOLATED_CONSTRUCTION_PASS',table_sha256=TABLE,source_sha256=SOURCE,native_sha256=NATIVE,baseline_archive_sha256=sha(archive),baseline_members_exact=True,independently_applied_allocation_stages=checks,upstream_to_candidate_lineage_receipt_sha256=sha(built/'lineage.json'),isolated_source_receipt_sha256=sha(src/'verification.json'),isolated_constructions_exactly_reproduce_stored_outputs=True,isolated_input_hashes=inputs,environment=dict(PYTHONPATH='',PYTHONNOUSERSITE='1',PYTHONDONTWRITEBYTECODE='1',only_listed_inputs_copied=True),historical_certified_seeds=certified,final_provenance_records_agree=True,checker_sha256=sha(Path(__file__)),scope='Accepted original219 archive members, exact declarative construction, independent edit replay and source checks, isolated reconstruction with standard library. Historical finite/discovery statuses are not upgraded; fresh218 runtime and final portable release replay are separate.')
 dump(OUT/'provenance_audit.json',result);dump(OUT/'provenance_isolation_paths.json',dict(root=str(temporary),commands=commands));print(json.dumps(result,indent=2))
if __name__=='__main__':
 if not __debug__:raise RuntimeError('Run without -O, -OO or PYTHONOPTIMIZE')
 main()
