#!/usr/bin/env python3
"""Owned, offline, dependency-closed reproduction of the 214-state search result.
This does not claim a 214-state calibrated machine. Inputs are inert data.
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
 m={int(a):int(b)for a,b in json.loads((R/'inputs/NATIVE_TO_LEGACY.json').read_text()).items()};assert len(set(m.values()))==len(m)
 for q in sorted({q for q,b in T}|{z for w,d,z in T.values()}):
  if q not in m:m[q]=max(m.values())+1
 return{(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in T.items()}
def main():
 assert __debug__ and not sys.flags.optimize and not os.environ.get('PYTHONOPTIMIZE'),'Enable assertions'
 ap=argparse.ArgumentParser();ap.add_argument('--runtime',action='store_true');ap.add_argument('--work',type=Path);ap.add_argument('--no-manifest',action='store_true',help=argparse.SUPPRESS);args=ap.parse_args()
 if not args.no_manifest:
  for x in json.loads((R/'MANIFEST.json').read_text())['files']:
   p=R/x['path'];assert p.is_file()and p.stat().st_size==x['bytes']and H(p)==x['sha256'],x['path']
 W=args.work or Path(tempfile.mkdtemp(prefix='transfer214-replay-'))
 if args.work:W.mkdir(parents=True,exist_ok=False)
 started=time.monotonic();out={'status':'RUNNING','target214_met':False,'received_code_executed':False}
 # Exact new source: delete the old DROP selector and compose its closed body
 # with two old NIP bodies. No search, allocator or received program is run.
 oldsites=json.loads((R/'inputs/baseline215.sites.json').read_text());old=B.tree(oldsites)
 assert unique(old)==202
 nip=at(old,'111');drop=at(old,'110101')
 small=replace(old,'1101',(at(old,'11010010'),('CB',1)))
 new=replace(small,'111',((drop,nip),nip));sites=B.flatten(new)
 assert B.compact(sites)==(R/'source/transfer201.sites.json').read_bytes()
 assert unique(new)==201 and len(sites)==4775
 leaves={x[0]for x in sites};prefixes={p[:j]for p in leaves for j in range(len(p))}
 assert not leaves&prefixes and len(prefixes)==len(leaves)-1
 assert all(p+b in leaves|prefixes for p in prefixes for b in '01')
 assert sum(2 if op=='CD'else 1 for p,op,k in sites)==6209
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
 G=B.cfg(sites);assert structured(new)==G
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
 # Pinned literal row construction and canonical state bijection.
 recipe=json.loads((R/'checks/table_recipe.json').read_text());assert H(R/'inputs/baseline215.native.tm')==recipe['input_sha256']
 T=B.parse_table(R/'inputs/baseline215.native.tm')
 for x in recipe['rows']:
  k=tuple(x['key']);assert T.get(k)==(None if x['old']is None else tuple(x['old']))
  if x['new']is None:del T[k]
  else:T[k]=tuple(x['new'])
 assert B.encode(T)==(R/'machine/transfer215.native.tm').read_bytes()
 assert H(R/'machine/transfer215.native.tm')==recipe['output_sha256']=='1f8194fa49a638857ecf5b4f69b1ae92cb47d11d1a74e952bbb91049c893a836'
 qs={q for q,b in T};assert len(qs)==215 and len(T)==430 and 254 not in qs
 assert all((q,b)in T for q in qs for b in [0,1])and all(z in qs|{254}for w,d,z in T.values())
 m={q:i for i,q in enumerate(sorted(qs))};m[254]=215;K=I.table(R/'machine/transfer215.tm')
 assert K=={(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in T.items()}
 reach={0};todo=[0]
 for q in todo:
  for b in [0,1]:
   z=T[q,b][2]
   if z!=254 and z not in reach:reach.add(z);todo.append(z)
 assert reach==qs
 # Full blank startup: sparse, dense and canonical lockstep, not a window.
 f=json.loads((R/'evidence/blank_frames.json').read_text())[0]['frames'][0]
 assert f['steps']==68442 and f['logical']==[1,11,2,0,0,0,0,0,0]and f['spares']==[1]*59
 assert sites[55][0]=='110100100101010'
 expected={x-2 for x in I.frame(sites[55][0],f['logical'],f['spares'],0)}
 assert expected==set(f['one_cells'])
 q=h=cq=ch=q2=h2=0;ones=set();con=set();left=bytearray(4096);right=bytearray(4096)
 for tick in range(68442):
  w,d,q=T[q,int(h in ones)]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d;cw,cd,cq=K[cq,int(ch in con)]
  if cw:con.add(ch)
  else:con.discard(ch)
  ch+=cd;assert(cq,ch,con)==(m[q],h,ones)
  cells,i=(right,h2)if h2>=0 else(left,-1-h2);assert 0<=i<len(cells)
  w,d,q2=T[q2,cells[i]];cells[i]=w;h2+=d
 dense={i for i,b in enumerate(right)if b}|{-i-1 for i,b in enumerate(left)if b}
 assert(q,h)==(q2,h2)==(84,-2)and ones==dense==expected
 out['startup']={'status':'EXACT_FRAME_PASS','steps':68442,'source_ordinal':55,'head':h,'logical':f['logical'],'spares':59,'one_cells':len(ones),'sparse_dense_and_canonical_agree':True}
 # Source prefix identifies this exact frame as a point inside the first AX.
 rec=json.loads((R/'evidence/ax_bootstrap_match.json').read_text());pc=25;reg=[1,0,4,0,0,0,0,0,0];trace=[]
 for tick in range(174):
  trace.append([pc,reg.copy()]);op,k,edges=G[pc]
  if op=='CI':reg[k]+=1;pc=edges[0]
  elif op=='CD':
   if reg[k]:reg[k]-=1;pc=edges[1]
   else:pc=edges[0]
  else:assert op in ('CB','CC');pc=edges[0]
 assert pc==55 and reg==f['logical']
 assert rec['trace']==trace and rec['entry_ordinal']==25 and rec['exit_ordinal']==55 and rec['steps']==174
 out['ax_prefix']={'status':'EXACT_SOURCE_PREFIX_MATCH','steps':174,'entry_ordinal':25,'exit_ordinal':55,'entry_registers':[1,0,4,0,0,0,0,0,0],'exit_registers':reg}
 # Reproduce the narrow negative: the literal deleted-helper table has a
 # finite path to an outward self-loop on every possible designated start.
 U=I.table(R/'negative_controls/rejected_delete301_214.native.tm');records=json.loads((R/'evidence/delete301_all_starts.json').read_text())['results']
 assert len(U)==428 and sorted(r['start']for r in records)==sorted({q for q,b in U})
 for r in records:
  q=r['start'];h=0;ones=set()
  for tick in range(r['steps']):
   b=int(h in ones);w,d,z=U[q,b]
   assert r['trace'][tick]==[q,h,b,w,d,z]
   if w:ones.add(h)
   else:ones.discard(h)
   q=z;h+=d
  assert(q,h,sorted(ones))==(r['state'],r['head'],r['ones'])
  w,d,z=U[q,0];assert [w,d,z]==r['ray_action']and z==q and h not in ones
  assert all(x<h if d==1 else x>h for x in ones)
 out['rejected_delete301']={'status':'ALL_STARTS_OUTWARD_RAYS','states':214,'starts':len(records),'maximum_prefix_steps':max(r['steps']for r in records)}
 import check_raw214_counterexample as X
 raw_concrete=X.verify(R);assert raw_concrete==json.loads((R/'evidence/raw214_counterexample.json').read_text())
 out['raw214_concrete_counterexample']=raw_concrete
 # Finite corroborations are rerun in the fresh output directory. They do
 # not replace either written universal proof.
 for file,receipt,reference in [('check_nip_transfer.py','NIP_TRANSFER_SYMBOLIC_CHECK.json','nip_transfer_symbolic.json'),('check_transfer_credit.py','TRANSFER_CREDIT_CHECK.json','credit_finite.json')]:
  shutil.copy2(R/'checks'/file,W/file)
  subprocess.run([sys.executable,str(W/file)],check=True,cwd=W)
  assert json.loads((W/receipt).read_text())==json.loads((R/'evidence'/reference).read_text())
 out['finite_command_checks']={'status':'PASS','symbolic_contract_cases':51,'credit_candidates':500000,'credit_diagonals':997}
 cert=C.verify(C.read_json(R/'inputs/dominated_rho8_full_certificate.json'),True)[0]
 assert cert['verified']and cert['proof_nodes']==3728 and cert['term_table_nodes']==5160
 out['inherited_dominated_certificate']=cert
 out['finite']={'status':'PASS','source_nodes':201,'source_occurrences':4775,'working_states':215,'rows':430,'all_states_graph_reachable':True,'source_cfg_independent_match':True,'closed_body_cfg_transports':4,'selector_zero_transfer_one_mp_at_least_two_ax':True}
 print('PASS: exact source and table, canonical map, full blank frame, AX prefix, 214-state all-start ray rejection, finite corroboration and inherited certificate',flush=True)
 if args.runtime:
  import symbolic_runtime as S
  T=mapped(T);lemmas,blocks=S.prove_blocks(T);cases=[];rows=set()
  for i,site in enumerate(sites):
   for pos in ((False,True)if site[1]=='CD'else(False,)):
    c=S.case(T,lemmas,site,pos);rows.update(c.pop('rows'));c.pop('trace');cases.append(dict(index=i,positive=pos,**c))
   if i%500==0:print('Runtime:',len(cases),'cases',flush=True)
  data=(json.dumps(cases,indent=2)+'\n').encode();(W/'runtime_cases.json').write_bytes(data)
  assert data==gzip.decompress((R/'evidence/runtime_cases.json.gz').read_bytes())
  r={'status':'ALL_NATURAL_RUNTIME_PASS','cases':len(cases),'symbolic_rules':sum(c['symbolic_steps']for c in cases),'row_coverage':len(rows),'minimum_duration':min(c['duration'][0]for c in cases),'cases_sha256':hashlib.sha256(data).hexdigest(),'fresh_block_certificates':blocks}
  original=json.loads((R/'evidence/runtime.json').read_text())
  for key in r:assert json.loads(json.dumps(r[key]))==original[key],key
  assert r['cases']==6209 and r['symbolic_rules']==1611489 and r['row_coverage']==430
  out['runtime']=r
  # A fresh counterexample to the raw 214 allocation, not mere failure of
  # the final table's checksum: it fails its own first CI8 arithmetic case.
  raw=mapped(I.table(R/'negative_controls/rejected_raw214.native.tm'));rl,_=S.prove_blocks(raw);failure=None
  for i,site in enumerate(sites):
   for pos in ((False,True)if site[1]=='CD'else(False,)):
    try:S.case(raw,rl,site,pos)
    except (AssertionError,KeyError)as e:failure={'index':i,'site':site,'positive':pos,'error':repr(e)};break
   if failure:break
  assert failure is not None;out['rejected_raw214']=failure
 out.update(status='FULL_REPLAY_PASS'if args.runtime else'FINITE_REPLAY_PASS',seconds=time.monotonic()-started)
 dump(W/'replay.json',out);print(json.dumps({k:v for k,v in out.items()if k not in ('runtime','inherited_dominated_certificate')},indent=2));print('Receipts:',W)
if __name__=='__main__':main()
