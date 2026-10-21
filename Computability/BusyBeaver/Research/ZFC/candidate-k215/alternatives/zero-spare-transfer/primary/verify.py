#!/usr/bin/env python3
"""Owned offline reproduction of the append-zero transfer 215-state candidate.
The source language is unchanged; spare policy and blank startup are new. Inputs are inert data.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,os,sys,tempfile,time,subprocess,shutil
R=Path(__file__).resolve().parent;sys.path.insert(0,str(R/'checks'))
import source_utils as B
import independent_runtime as I
import check_fixed_certificate as C
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def at(t,p):
 for b in p:t=t[int(b)]
 return t
def replace(t,p,n):
 if not p:return n
 return (replace(t[0],p[1:],n),t[1])if p[0]=='0'else(t[0],replace(t[1],p[1:],n))
def unique(t):
 found=set()
 def go(n):
  if n in found:return
  found.add(n)
  if not B.leaf(n):go(n[0]);go(n[1])
 go(t);return len(found)
def mapped(T):
 m={int(a):int(b)for a,b in json.loads((R/'inputs/NATIVE_TO_LEGACY.json').read_text()).items()};assert len(set(m.values()))==len(m) and m[84]==96 and m[254]==254
 for q in sorted({q for q,b in T}|{z for w,d,z in T.values()}):
  if q not in m:m[q]=max(m.values())+1
 return{(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in T.items()}
def main():
 if not __debug__ or sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'):
  raise RuntimeError('Enable assertions: do not use -O or PYTHONOPTIMIZE')
 ap=argparse.ArgumentParser();ap.add_argument('--runtime',action='store_true');ap.add_argument('--work',type=Path);ap.add_argument('--no-manifest',action='store_true',help=argparse.SUPPRESS);args=ap.parse_args()
 if not args.no_manifest:
  for x in json.loads((R/'MANIFEST.json').read_text())['files']:
   p=R/x['path'];assert p.is_file()and p.stat().st_size==x['bytes']and H(p)==x['sha256'],x['path']
 W=args.work.resolve() if args.work else Path(tempfile.mkdtemp(prefix='zero-spare215-replay-'))
 if args.work:W.mkdir(parents=True,exist_ok=False)
 started=time.monotonic();out={'status':'RUNNING','candidate':'zero-spare-transfer215','target214_met':False,'received_code_executed':False,'proof_assistant_endpoint_claimed':False}
 # Exact new source: delete the old DROP selector and compose its closed body
 # with two old NIP bodies. No search, allocator or received program is run.
 oldsites=json.loads((R/'inputs/baseline215.sites.json').read_text());old=B.tree(oldsites)
 assert unique(old)==202
 nip=at(old,'111');drop=at(old,'110101')
 small=replace(old,'1101',(at(old,'11010010'),('CB',1)))
 new=replace(small,'111',((drop,nip),nip));sites=B.flatten(new)
 assert B.compact(sites)==(R/'source/transfer201.sites.json').read_bytes()
 assert unique(new)==201 and len(sites)==4775
 assert H(R/'source/transfer201.sites.json')=='05e7caa159d95cdf9ee254d313c44c52369ac91e52cbc23d54b15f0b64b95922'
 leaves={x[0]for x in sites};prefixes={p[:j]for p in leaves for j in range(len(p))}
 assert not leaves&prefixes and len(prefixes)==len(leaves)-1
 assert all(p+b in leaves|prefixes for p in prefixes for b in '01')
 assert sum(2 if op=='CD'else 1 for p,op,k in sites)==6209
 assert max(map(len,leaves))==44 and all(set(p)<={'0','1'} and len(p)<=64 for p in leaves)
 assert all(op in ('CI','CD','CB','CC','CH') and (k is None if op=='CH'else type(k)is int and (0<=k<9 if op in ('CI','CD')else k>=1))for p,op,k in sites)
 # Two independent ways of calculating the structured source graph.
 def structured(t):
  from functools import lru_cache
  @lru_cache(None)
  def length(n):return 1 if B.leaf(n)else length(n[0])+length(n[1])
  N=length(t);rows=[]
  def go(n,i,bs,cs):
   if B.leaf(n):
    op,k=n;target=lambda a,j:a[-j]%N if len(a)>=j else 0
    e=[]if op=='CH'else[target(bs,k)]if op=='CB'else[target(cs,k)]if op=='CC'else[target(bs,1),(i+1)%N]if op=='CD'else[(i+1)%N]
    assert len(rows)==i;rows.append([op,None if op in ('CB','CC')else k,e]);return
   mid=i+length(n[0]);go(n[0],i,bs+[i+length(n)],cs);go(n[1],mid,bs,cs+[i])
  go(t,0,[],[]);return rows
 G=B.cfg(sites);assert structured(new)==G and structured(old)==B.cfg(oldsites)
 # Closed bodies are not identified merely by equal subtree hashes: compare
 # each primitive and every local/exterior edge under ordinal translation.
 oldG=B.cfg(oldsites)
 def local_graph(ss,gg,prefix):
  ids=[i for i,x in enumerate(ss)if x[0].startswith(prefix)];a,b=min(ids),max(ids)+1
  assert ids==list(range(a,b))
  local=[]
  for i in ids:
   op,k,e=gg[i];targets=[]
   for z in e:
    assert a<=z<b or z==b%len(ss),(prefix,i,z,a,b)
    targets.append(z-a if a<=z<b else 'EXIT')
   local.append([op,k,targets])
  return local
 for oldp,newp in [('11010010','11010'),('110101','11100'),('111','11101'),('111','1111')]:
  assert local_graph(oldsites,oldG,oldp)==local_graph(sites,G,newp),(oldp,newp)
 assert G[23]==['CD',3,[4697,24]]and G[24]==['CD',3,[4590,25]]
 assert G[4696]==['CB',None,[0]]
 # Every physical prefix successor resolves to the structured source edge.
 first={}
 for i,(p,op,k)in enumerate(sites):
  for j in range(len(p)+1):first.setdefault(p[:j],i)
 def resolve(p):
  while p not in first:assert p.endswith('0');p=p[:-1]
  return first[p]
 bindings=[]
 for i,(p,op,k)in enumerate(sites):
  for positive in ((False,True)if op=='CD'else(False,)):
   if op=='CH':dest=None
   elif op=='CI'or(op=='CD'and positive):dest=resolve(I.inc(p)[0])
   elif op in ('CD','CB'):dest=resolve(I.inc(I.strip(p,'0',1 if op=='CD'else k))[0])
   else:dest=resolve(I.strip(p,'1',k))
   expected=None if op=='CH'else G[i][2][int(positive)]if op=='CD'else G[i][2][0]
   assert dest==expected,(i,op,positive,dest,expected)
   bindings.append([i,positive,dest])
 assert len(bindings)==6209
 binding_bytes=B.compact(bindings)
 assert binding_bytes==(R/'evidence/source_contract_bindings.json').read_bytes()
 (W/'source_contract_bindings.json').write_bytes(binding_bytes)
 out['source_binding']={'status':'PASS','source_nodes':201,'primitive_occurrences':4775,'guards':6209,'independent_cfg_match':True,'closed_body_cfg_transports':4,'physical_source_contract_bindings':len(bindings),'bindings_sha256':hashlib.sha256(binding_bytes).hexdigest(),'maximum_source_depth':44}
 # Pinned literal row construction and canonical state bijection.
 recipe=json.loads((R/'checks/table_recipe.json').read_text());assert H(R/'inputs/baseline215.native.tm')==recipe['input_sha256']
 T=B.parse_table(R/'inputs/baseline215.native.tm')
 for x in recipe['rows']:
  k=tuple(x['key']);assert T.get(k)==(None if x['old']is None else tuple(x['old']))
  if x['new']is None:del T[k]
  else:T[k]=tuple(x['new'])
 assert B.encode(T)==(R/'inputs/append_one_transfer215.native.tm').read_bytes()
 assert H(R/'inputs/append_one_transfer215.native.tm')==recipe['output_sha256']=='1f8194fa49a638857ecf5b4f69b1ae92cb47d11d1a74e952bbb91049c893a836'
 assert T[198,0]==(1,-1,40);T[198,0]=(0,-1,40)
 assert B.encode(T).replace(b'#! start 0\n',b'#! start 74\n',1)==(R/'machine/zero_spare_transfer215.native.tm').read_bytes()
 assert H(R/'machine/zero_spare_transfer215.native.tm')=='29a6ed4a594d7f974cf267a9e6b665af34c9afd8dd7abbbecf0b538ecab151e0'
 assert H(R/'machine/zero_spare_transfer215.tm')=='60eae1c30d214f71c65a207087dc716ba4cdad2a1a62c51e9e107434a0ceb4f1'
 qs={q for q,b in T};assert len(qs)==215 and len(T)==430 and 254 not in qs
 assert all((q,b)in T for q in qs for b in [0,1])and all(z in qs|{254}for w,d,z in T.values())
 m={74:0};m.update({q:i+1 for i,q in enumerate(sorted(qs-{74}))});m[254]=215;K=I.table(R/'machine/zero_spare_transfer215.tm')
 assert K=={(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in T.items()}
 assert m=={int(q):z for q,z in json.loads((R/'machine/native_to_canonical.json').read_text()).items()}
 canon=json.loads((R/'machine/canonicalization.json').read_text())
 assert canon=={'native_start':74,'canonical_start':0,'native_halt':254,'canonical_halt':215,'native_to_canonical':{str(q):z for q,z in m.items()}}
 assert set(q for q,b in K)==set(range(215))
 reach={74};todo=[74]
 for q in todo:
  for b in [0,1]:
   z=T[q,b][2]
   if z!=254 and z not in reach:reach.add(z);todo.append(z)
 assert reach==qs
 # Full blank startup: sparse, dense and canonical lockstep, not a window.
 f=json.loads((R/'evidence/blank_frames.json').read_text())[0]['frames'][0]
 assert f['steps']==73172 and f['logical']==[0,6,0,0,1,1,10,1,0]and f['spares']==[0,0,1]+[0]*62
 assert sites[119][0]=='11010011000110110110'
 expected={x-2 for x in I.frame(sites[119][0],f['logical'],f['spares'],0)}
 assert expected==set(f['one_cells'])
 q=q2=74;h=cq=ch=h2=0;ones=set();con=set();left=bytearray(4096);right=bytearray(4096)
 for tick in range(73172):
  w,d,q=T[q,int(h in ones)]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d;cw,cd,cq=K[cq,int(ch in con)]
  if cw:con.add(ch)
  else:con.discard(ch)
  ch+=cd;assert(cq,ch,con)==(m[q],h,ones)
  cells,i=(right,h2)if h2>=0 else(left,-1-h2);assert 0<=i<len(cells)
  w,d,q2=T[q2,cells[i]];cells[i]=w;h2+=d
  assert(q2,h2)==(q,h)
 dense={i for i,b in enumerate(right)if b}|{-i-1 for i,b in enumerate(left)if b}
 assert(q,h)==(q2,h2)==(84,-2)and ones==dense==expected
 assert len(ones)==107
 cb=json.loads((R/'evidence/canonical_blank_check.json').read_text())
 assert cb['status']=='PASS' and cb['native_sha256']==H(R/'machine/zero_spare_transfer215.native.tm') and cb['canonical_sha256']==H(R/'machine/zero_spare_transfer215.tm')
 assert (cb['native_start'],cb['canonical_start'],cb['native_exit_state'],cb['canonical_exit_state'],cb['head'],cb['steps'])==(74,0,84,81,-2,73172)
 assert cb['working_states']==215 and cb['rows']==430 and cb['all_graph_states_reachable']
 assert cb['one_cells']==sorted(ones) and cb['spare_count']==65 and cb['spares']==f['spares']
 ir=json.loads((R/'evidence/independent_zero_spare_startup_check.json').read_text());iv=ir['variants'][0]
 assert ir['status']=='PASS' and iv['table_sha256']==cb['native_sha256'] and iv['source_sha256']==H(R/'source/transfer201.sites.json')
 assert iv['blank_steps']==73172 and iv['full_frame_exact'] and iv['source_ordinal']==119 and iv['source_address']==sites[119][0] and iv['logical']==f['logical']
 assert (ir['protected_heads'],ir['opaque_tail'],ir['known_credit_debt_at_N0'],ir['permanent_margin'])==(8,171,3,5)
 out['startup']={'status':'EXACT_FRAME_PASS','steps':73172,'source_ordinal':119,'native_state':84,'canonical_state':81,'head':h,'gap':0,'logical':f['logical'],'spares':65,'one_cells':len(ones),'sparse_dense_and_canonical_agree':True}
 # Source prefix identifies this exact frame as a point inside the first AX.
 rec=json.loads((R/'evidence/ax_bootstrap_match.json').read_text())['attempts'][0];pc=25;reg=[0,0,0,0,1,1,0,0,0];trace=[]
 for tick in range(177):
  trace.append([pc,reg.copy()]);op,k,edges=G[pc]
  if op=='CI':reg[k]+=1;pc=edges[0]
  elif op=='CD':
   if reg[k]:reg[k]-=1;pc=edges[1]
   else:pc=edges[0]
  else:assert op in ('CB','CC');pc=edges[0]
 assert pc==119 and reg==f['logical']
 assert rec['trace']==trace and rec['entry_ordinal']==25 and rec['exit_ordinal']==119 and rec['steps']==177
 out['ax_prefix']={'status':'EXACT_SOURCE_PREFIX_MATCH','steps':177,'entry_ordinal':25,'exit_ordinal':119,'entry_registers':[0,0,0,0,1,1,0,0,0],'exit_registers':reg}
 # Finite corroborations are rerun in the fresh output directory. They do
 # not replace either written universal proof.
 for file,receipt,reference in [('check_nip_transfer.py','NIP_TRANSFER_SYMBOLIC_CHECK.json','nip_transfer_symbolic.json'),('check_transfer_credit.py','TRANSFER_CREDIT_CHECK.json','credit_finite.json')]:
  shutil.copy2(R/'checks'/file,W/file)
  subprocess.run([sys.executable,'-I','-B',str(W/file)],check=True,cwd=W)
  assert json.loads((W/receipt).read_text())==json.loads((R/'evidence'/reference).read_text())
 credit=json.loads((R/'evidence/credit_finite.json').read_text());assert credit['small_credits'][0]['required_credit']==3 and credit['minimum_global_command_prefix_balance']==-3
 out['finite_command_checks']={'status':'PASS','symbolic_contract_cases':51,'credit_candidates':500000,'credit_diagonals':997,'cutoff0_required_credit':3,'initial_safe_heads':8,'permanent_margin':5}
 cert=C.verify(C.read_json(R/'inputs/dominated_rho8_full_certificate.json'),True)[0]
 assert cert['verified']and cert['proof_nodes']==3728 and cert['term_table_nodes']==5160
 out['inherited_dominated_certificate']=cert
 out['finite']={'status':'PASS','source_nodes':201,'source_occurrences':4775,'working_states':215,'rows':430,'appended_spare_value':0,'native_start':74,'all_states_graph_reachable':True,'source_cfg_independent_match':True,'closed_body_cfg_transports':4,'selector_zero_transfer_one_mp_at_least_two_ax':True}
 print('PASS: exact source and table, canonical map, full start74 blank frame, 177-step AX prefix, finite corroboration and inherited certificate',flush=True)
 if args.runtime:
  import symbolic_runtime as S
  T=mapped(T);lemmas,blocks=S.prove_blocks(T);cases=[];rows=set()
  schema_rows={tuple(event[1][:2])for block in blocks for event in block['trace']}
  assert schema_rows<=set(T)
  for i,site in enumerate(sites):
   for pos in ((False,True)if site[1]=='CD'else(False,)):
    c=S.case(T,lemmas,site,pos,append=0);rows.update(c.pop('rows'));c.pop('trace');cases.append(dict(index=i,positive=pos,**c))
   if i%500==0:print('Runtime:',len(cases),'cases',flush=True)
  data=(json.dumps(cases,indent=2)+'\n').encode();(W/'runtime_cases.json').write_bytes(data)
  assert data==gzip.decompress((R/'evidence/runtime_cases.json.gz').read_bytes())
  r={'status':'ALL_NATURAL_RUNTIME_PASS','cases':len(cases),'symbolic_rules':sum(c['symbolic_steps']for c in cases),'row_coverage':len(rows),'minimum_duration':min(c['duration'][0]for c in cases),'cases_sha256':hashlib.sha256(data).hexdigest(),'fresh_block_certificates':blocks}
  original=json.loads((R/'evidence/runtime.json').read_text())
  for key in r:assert json.loads(json.dumps(r[key]))==original[key],key
  assert r['cases']==6209 and r['symbolic_rules']==1611489 and r['row_coverage']==430
  assert rows|schema_rows==set(T) and rows==set(T)
  assert original['appended_spare_value']==0 and original['table_sha256']==H(R/'machine/zero_spare_transfer215.native.tm') and original['source_sha256']==H(R/'source/transfer201.sites.json')
  assert original['kernel_sha256']==H(R/'checks/symbolic_runtime.py') and original['helper_sha256']==H(R/'checks/independent_runtime.py')
  assert original['working_states']==215 and original['table_rows']==430 and original['source_sites']==4775 and original['expected_cases']==6209 and original['failure'] is None
  coverage={'status':'ALL_ROWS_PASS','label_system':'legacy runtime labels','direct_case_rows':sorted(rows),'one_block_schema_rows':sorted(schema_rows),'covered_rows':sorted(rows|schema_rows),'table_rows':sorted(T),'direct_count':len(rows),'schema_count':len(schema_rows),'union_count':len(rows|schema_rows),'all_430_rows_covered':True}
  assert json.loads(json.dumps(coverage))==json.loads((R/'evidence/runtime_row_coverage.json').read_text())
  dump(W/'runtime_row_coverage.json',coverage)
  dump(W/'runtime.json',r)
  out['runtime']=r
 out.update(status='FULL_REPLAY_PASS'if args.runtime else'FINITE_REPLAY_PASS',seconds=time.monotonic()-started)
 dump(W/'replay.json',out);print(json.dumps({k:v for k,v in out.items()if k not in ('runtime','inherited_dominated_certificate')},indent=2));print('Receipts:',W)
if __name__=='__main__':main()
