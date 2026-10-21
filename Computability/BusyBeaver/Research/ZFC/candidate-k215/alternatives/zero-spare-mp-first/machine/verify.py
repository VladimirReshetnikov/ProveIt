#!/usr/bin/env python3
"""Portable exact-byte verification; --runtime rederives the unbounded census."""
from pathlib import Path
import argparse,gzip,hashlib,importlib.util,json,os,subprocess,sys,tempfile,time
if not __debug__ or sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'):
 raise RuntimeError('Verification requires assertions; omit -O and PYTHONOPTIMIZE')
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parent
sys.path[:0]=[str(R/'parent/code'),str(R/'parent/reference/transfer-parent/checks')]
import source_language as L,source_utils as U,independent_runtime as I
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
def require(x,message):
 if not x:raise ValueError(message)
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def independent_frame(path,regs,spares,gap,head):
 values=[regs[k] for k in(2,8,1,4,3,7,0,5,6)]+list(spares)
 one={head-1,head+64+gap}|{head+i for i,b in enumerate(path)if b=='1'}
 p=head+65+gap
 for v in values:
  require(type(v)is int and v>=0,'Frame natural value')
  one.update(range(p+1,p+v+2));p+=v+2
 return one

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--runtime',action='store_true');ap.add_argument('--out',type=Path);a=ap.parse_args()
 if a.out:a.out.mkdir(parents=True,exist_ok=False)
 W=a.out or Path(tempfile.mkdtemp(prefix='mp-first-zero-'))
 require((R/'manifest.json').exists(),'Missing manifest')
 if(R/'manifest.json').exists():
  inventory=read(R/'manifest.json')['files']
  actual={str(p.relative_to(R))for p in R.rglob('*')if p.is_file()and p!=R/'manifest.json'}
  require(actual=={x['path']for x in inventory},'Manifest inventory')
  for x in inventory:require(H(R/x['path'])==x['sha256'],'Manifest '+x['path'])
 # Original source reconstruction includes two independent control-flow resolvers.
 spec=importlib.util.spec_from_file_location('parent_verify',R/'parent/verify.py');PV=importlib.util.module_from_spec(spec);spec.loader.exec_module(PV)
 ss,G,old,_,_,parent_check=PV.reconstruction()
 require((R/'sites.json').read_bytes()==(R/'parent/machine/sites215.json').read_bytes(),'Exact source identity')
 require(H(R/'sites.json')=='8ddb942f0f1d8e2e3b12ab7217c7232eb553cd288fca38dbf9b0eded73893dd5','Pinned source')
 require(H(R/'parent/machine/t215.native.tm')=='485ca26885508bdaf76ecd8f46827b64518ca1d9e32de81b2a8ac2904a49d9f2','Pinned table parent')
 require(old[198,0]==(1,-1,40),'Old spare row');T=old.copy();T[198,0]=(0,-1,40)
 native='#! start 74\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))
 require(native==(R/'candidate.native.tm').read_text(),'Exact one-row construction')
 qs={q for q,b in T};require(len(qs)==215 and len(T)==430 and 254 not in qs,'215 working states')
 require(all((q,b)in T for q in qs for b in(0,1)),'Total binary table')
 require(all(w in(0,1)and d in(-1,1)and z in qs|{254}for w,d,z in T.values()),'Valid actions')
 reach={74};todo=[74]
 for q in todo:
  for b in(0,1):
   z=T[q,b][2]
   if z!=254 and z not in reach:reach.add(z);todo.append(z)
 require(reach==qs,'All states graph reachable')
 m={int(k):int(v)for k,v in read(R/'canonicalization.json').items()}
 require(m[74]==0 and m[254]==215 and set(m)==qs|{254}and set(m.values())==set(range(216)),'Complete dense bijection')
 K=I.table(R/'candidate.tm');require(K=={(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in T.items()},'Dense literal table')
 require((R/'candidate.tm').read_text().splitlines()[0]=='#! start 0','Dense start')
 # Literal blank run in two labelings and two independent tape representations.
 st=json.loads(gzip.decompress((R/'startup.json.gz').read_bytes()))
 require(st['start']==74 and st['steps']==73172 and len(st['trace'])==73172,'Startup extent')
 q=74;h=0;cq=ch=0;ones=set();con=set();dq=74;dh=0;left=bytearray(4096);right=bytearray(4096)
 for event in st['trace']:
  b=int(h in ones);w,d,z=T[q,b];require(event==[q,h,b,w,d,z],'Literal transition trace')
  ones.add(h)if w else ones.discard(h);q=z;h+=d
  cw,cd,cz=K[cq,int(ch in con)];con.add(ch)if cw else con.discard(ch);cq=cz;ch+=cd
  require((cq,ch,con)==(m[q],h,ones),'Dense/native lockstep')
  cells,j=(right,dh)if dh>=0 else(left,-dh-1);require(j<len(cells),'Independent tape capacity')
  dw,dd,dq=T[dq,cells[j]];cells[j]=dw;dh+=dd
 dense={i for i,b in enumerate(right)if b}|{-i-1 for i,b in enumerate(left)if b}
 require((q,h)==(dq,dh)==(84,-2)and ones==dense==set(st['one_cells']),'Complete final blank tape')
 require(st['ordinal']==119 and st['pc']==ss[119][0]=='11010011000110110110'and st['gap']==0,'Startup source address')
 require(st['registers']==[0,6,0,0,1,1,10,1,0]and len(st['spares'])==65,'Startup registers and spares')
 require(ones==independent_frame(st['pc'],st['registers'],st['spares'],0,-2)=={x-2 for x in I.frame(st['pc'],st['registers'],st['spares'],0)},'Independent whole-tape frames')
 # Match exact 177-step synthetic AX prefix against both source CFG implementations.
 src=read(R/'source_prefix.json');g=U.cfg(ss);pc=25;reg=[0,0,0,0,1,1,0,0,0];trace=[]
 require(src['entry']==25 and src['seed']==reg and src['steps']==177,'Source-prefix entry')
 for tick in range(177):
  trace.append([pc,reg.copy()]);op,k,edges=g[pc];effect,targets=G[pc]
  require(edges==targets,'Dual source successors')
  if op=='CI':require(effect==['increment',k],'Dual source effect');reg[k]+=1;pc=edges[0]
  elif op=='CD':
   require(effect==['decrement',k],'Dual source effect')
   if reg[k]:reg[k]-=1;pc=edges[1]
   else:pc=edges[0]
  else:require(op in('CB','CC')and effect==['identity'],'Nonhalting AX source step');pc=edges[0]
 require((pc,reg)==(119,st['registers'])and trace==src['trace'],'Exact AX prefix')
 independent=W/'independent_startup.json'
 subprocess.run([sys.executable,'-B',str(R/'independent_review/check_startup.py'),'--out',str(independent)],check=True,stdout=subprocess.PIPE,text=True)
 require(read(independent)==read(R/'independent_review/startup_review.json'),'Fresh independent startup receipt')
 novelty=W/'novelty.json'
 subprocess.run([sys.executable,'-B',str(R/'independent_review/check_candidate_novelty.py'),str(R/'candidate.native.tm'),'--out',str(novelty)],check=True,stdout=subprocess.PIPE,text=True)
 require(read(novelty)==read(R/'independent_review/novelty_review.json'),'Fresh complete pinned novelty census')
 # Finite indexing check, not a substitute for the inherited all-natural diagonal proof.
 def unpair(n):
  from math import isqrt
  s=(isqrt(8*n+1)-1)//2;y=n-s*(s+1)//2;return s-y,y
 def word(n):
  a,y=unpair(n)
  if a==0:k='MP';r=unpair(y)[1]
  elif a==1:k='S';r=y
  else:k='AX';r=unpair(unpair(y)[1])[1]
  return[k]+(word(r-1)if r else[])
 require([word(n)for n in range(3)]==[['MP'],['S'],['MP']],'New exceptional credit words')
 cases=json.loads(gzip.decompress((R/'runtime_cases.json.gz').read_bytes()));coverage=json.loads(gzip.decompress((R/'runtime_rows.json.gz').read_bytes()));rr=read(R/'runtime.json')
 expected=[(i,pos)for i,s in enumerate(ss)for pos in((False,True)if s[1]=='CD'else(False,))]
 require([(c['index'],c['positive'])for c in cases]==expected and len(cases)==6209,'Ordered complete runtime cases')
 require([(c['index'],c['positive'])for c in coverage]==expected,'Ordered runtime coverage')
 require(all(len(c['duration'])==13 and all(type(v)is int and v>=0 for v in c['duration'])and c['duration'][0]>0 for c in cases),'Positive affine runtime')
 require(rr['status']=='ALL_NATURAL_RUNTIME_PASS'and rr['cases']==6209 and rr['row_coverage']==430,'Saved complete runtime status')
 require(rr['symbolic_rules']==sum(c['symbolic_steps']for c in cases)and rr['minimum_duration']==min(c['duration'][0]for c in cases),'Saved runtime totals')
 require(rr['table_sha256']==H(R/'candidate.native.tm')and rr['source_sha256']==H(R/'sites.json'),'Runtime exact pins')
 require(len({tuple(row)for c in coverage for row in c['rows']})==430,'Saved full row coverage')
 out=dict(status='FAST_AUDIT_PASS',states=215,rows=430,source_metrics=parent_check['source'],startup_steps=73172,source_prefix_steps=177,initial_theorem_heads=8,conservative_debt=1,permanent_conservative_margin=7,guarded_cases=6209,comparison_tables=77,comparison_rooted_graphs=44,new_proof_assistant_endpoint=False,table_sha256=H(R/'candidate.native.tm'),source_sha256=H(R/'sites.json'))
 print(json.dumps(out),flush=True)
 if a.runtime:
  import symbolic_runtime as S
  lm={int(k):int(v)for k,v in read(R/'parent/reference/transfer-parent/inputs/NATIVE_TO_LEGACY.json').items()}
  require(len(set(lm.values()))==len(lm),'Injective helper mapping')
  for q in sorted(qs|{254}):
   if q not in lm:lm[q]=max(lm.values())+1
  Utable={(lm[q],b):(w,d,lm[z])for(q,b),(w,d,z)in T.items()};lemmas,blocks=S.prove_blocks(Utable);fresh=[];used=set();percase=[]
  for i,site in enumerate(ss):
   for positive in((False,True)if site[1]=='CD'else(False,)):
    c=S.case(Utable,lemmas,site,positive,append=0);rows=c.pop('rows');used.update(rows);percase.append(dict(index=i,positive=positive,rows=sorted(rows)));c.pop('trace');fresh.append(dict(index=i,positive=positive,**c))
   if i%500==0:print('Fresh cases',len(fresh),flush=True)
  require(json.loads(json.dumps(fresh))==cases,'Fresh proof cases match archive')
  require(json.loads(json.dumps(percase))==coverage,'Fresh per-case rows match archive')
  require(len(used)==430 and json.loads(json.dumps(blocks))==rr['blocks'],'Fresh block schemas and row coverage')
  (W/'runtime_cases.json.gz').write_bytes(gzip.compress(json.dumps(fresh).encode(),mtime=0));(W/'runtime_rows.json.gz').write_bytes(gzip.compress(json.dumps(percase).encode(),mtime=0));out['status']='FULL_RUNTIME_PASS'
 dump(W/'verification.json',out);print('Receipts:',W)
if __name__=='__main__':main()
