#!/usr/bin/env python3
"""Independent exact checker. Standard library only; valid under python -O.

This checker never imports the polynomial constructor. Polynomial identities
are expanded from serialized artifacts. A separate finite step executes the
pinned coefficient recipe in a temporary directory and compares integer bytes.
It does not check consistency or replace the inherited unbounded semantics.
"""
from pathlib import Path
from collections import defaultdict,Counter
from functools import lru_cache
import hashlib,gzip,json,math,shutil,subprocess,sys,tempfile
R=Path(__file__).resolve().parent
def require(x,message):
 if not x:raise ValueError(message)
def clean(p):return {m:c for m,c in p.items()if c}
def plus(p,q,factor=1):
 out=dict(p)
 for m,c in q.items():out[m]=out.get(m,0)+factor*c
 return clean(out)
def times(p,q):
 out=defaultdict(int)
 for m,c in p.items():
  for n,d in q.items():out[tuple(a+b for a,b in zip(m,n))]+=c*d
 return clean(out)
def scale(p,c):return clean({m:c*v for m,v in p.items()})
def power(p,n):
 out={(0,)*len(next(iter(p))):1}
 while n:
  if n&1:out=times(out,p)
  n//=2
  if n:p=times(p,p)
 return out
def number(c,dim=4):return {(0,)*dim:c}if c else {}
def var(j,dim=4):return {tuple(int(k==j)for k in range(dim)):1}
def table(raw):return {tuple(m):int(c)for m,c in raw}
def shift(p,axis,value):
 out=defaultdict(int)
 for m,c in p.items():
  for k in range(m[axis]+1):
   n=list(m);n[axis]=k;out[tuple(n)]+=c*math.comb(m[axis],k)*value**(m[axis]-k)
 return clean(out)
def translate(p):
 for axis,value in enumerate((3,1,1,3)):p=shift(p,axis,value)
 return p
def expression_setup():
 A,C,i,t=(var(k)for k in range(4));one=number(1)
 D=plus(times(plus(power(A,2),one,-1),power(C,2)),one)
 J=plus(scale(A,4),number(-5));e=times(times(i,J),C)
 F=plus(times(times(plus(D,one,-1),power(e,2)),power(D,2)),one)
 L=plus(plus(times(C,D),one),A,-1);G=plus(A,times(F,L));H=plus(C,times(F,t))
 I=plus(times(plus(power(G,2),one,-1),power(H,2)),one)
 return A,C,i,t,D,J,e,F,L,G,H,I
def expand_table(raw,values):
 powers={}
 def p(j,e):
  if (j,e)not in powers:powers[j,e]=power(values[j],e)
  return powers[j,e]
 result={}
 for mon,coef in raw:
  term=number(int(coef))
  for j,e in enumerate(mon):
   if e:term=times(term,p(j,e))
  result=plus(result,term)
 return result
def symbolic_dag(doc,out,cuts,dim):
 @lru_cache(None)
 def go(k):
  if k in cuts:return cuts[k]
  node=doc['nodes'][k];kind=node['kind']
  if kind=='literal':return number(node['value'],dim)
  require(kind in ('add','sub','mul'),'unexpected uncut leaf '+str(node))
  left,right=go(node['left']),go(node['right'])
  return times(left,right)if kind=='mul'else plus(left,right,-1 if kind=='sub'else 1)
 return go(out)
def canonical(doc,k):
 @lru_cache(None)
 def go(j):
  n=doc['nodes'][j];kind=n['kind']
  if kind in ('literal','variable','fixed'):key=(kind,n.get('value',n.get('name')))
  else:
   a,b=go(n['left']),go(n['right'])
   if kind in ('add','mul')and a>b:a,b=b,a
   key=(kind,a,b)
  return hashlib.sha256(repr(key).encode()).hexdigest()
 return go(k)
def source_leaders(base):
 recipes={x['name']:{tuple(t['powers'])+(0,0):t['coefficient']for t in x['terms']}for x in base['coefficient_recipes']}
 recipes['base_scale']={(0,0,0,0,1,0):1};recipes['threshold_scale']={(0,0,0,0,0,1):1}
 @lru_cache(None)
 def lead(k):
  n=base['nodes'][k];kind=n['kind']
  if kind=='literal':return (0,number(n['value'],6))
  if kind=='variable':return (1,number(1,6))
  if kind=='fixed':return (0,recipes[n['name']])
  da,a=lead(n['left']);db,b=lead(n['right'])
  if kind=='mul':return da+db,times(a,b)
  deg=max(da,db);out=plus(a if da==deg else {},b if db==deg else {},-1 if kind=='sub'else 1)
  require(out or deg==0,'unresolved leading cancellation')
  return deg,out
 result={}
 for name in ('R','N','A','K','V0','a0','Omega','E0'):
  deg,coef=lead(base['named_nodes'][name]);result[name]={'degree':deg,'leader':[[list(m),str(c)]for m,c in sorted(coef.items())]}
 return result
def check_binding():
 root=R/'upstream/31-sun10/coefficients';binding=json.loads((root/'COEFFICIENT_BINDING.json').read_text())
 for f in binding['files']:
  payload=(root/f['file']).read_bytes();data=gzip.decompress(payload)
  require(hashlib.sha256(payload).hexdigest()==f['gzip_sha256'],'compressed coefficient hash')
  require(hashlib.sha256(data).hexdigest()==f['sha256'],'coefficient hash')
  require(int.from_bytes(data,'little').bit_length()==f['bit_length'],'coefficient bit length')
 return {f['port']:f['bit_length']for f in binding['files']}
def reconstruct_coefficients():
 """Replay the finite source31 recipe in a temporary directory, never in upstream/."""
 root=R/'upstream/31-sun10/coefficients';binding=json.loads((root/'COEFFICIENT_BINDING.json').read_text())
 generator=root/'build_coefficients.py'
 require(hashlib.sha256(generator.read_bytes()).hexdigest()=='d8e33ab484512ccf742a1f2998dfdb4294e082a0f68a887b81194c1543c07bad','pinned coefficient generator')
 entries=[]
 with tempfile.TemporaryDirectory(prefix='nine-source31-')as directory:
  temp=Path(directory);(temp/'upstream').mkdir()
  shutil.copyfile(generator,temp/'build_coefficients.py')
  for name in ('k215_transitions.json','wang943_tiles.json'):
   shutil.copyfile(root/'upstream'/name,temp/'upstream'/name)
  subprocess.run([sys.executable,str(temp/'build_coefficients.py')],check=True,capture_output=True,text=True,timeout=60)
  rebuilt_binding=json.loads((temp/'COEFFICIENT_BINDING.json').read_text())
  require(rebuilt_binding['instance']==binding['instance']and rebuilt_binding['source_commit']==binding['source_commit'],'reconstructed binding identity')
  for entry in binding['files']:
   stored=(root/entry['file']).read_bytes();rebuilt=(temp/entry['file']).read_bytes()
   old_raw,new_raw=gzip.decompress(stored),gzip.decompress(rebuilt)
   require(new_raw==old_raw,'byte-exact reconstructed coefficient '+entry['port'])
   entries.append({'port':entry['port'],'raw_bytes':len(new_raw),'raw_byte_identical':True,'gzip_byte_identical':rebuilt==stored,'raw_sha256':hashlib.sha256(new_raw).hexdigest(),'rebuilt_gzip_sha256':hashlib.sha256(rebuilt).hexdigest(),'stored_gzip_sha256':hashlib.sha256(stored).hexdigest()})
 # Raw equality is the mathematical check. gzip streams may differ between
 # Python/zlib versions while representing exactly the same integer bytes.
 certificate={'status':'PASS','instance':binding['instance'],'source_commit':binding['source_commit'],'generator_sha256':hashlib.sha256(generator.read_bytes()).hexdigest(),'source_inputs':['upstream/k215_transitions.json','upstream/wang943_tiles.json'],'temporary_reconstruction':True,'raw_payloads_byte_identical':len(entries),'gzip_payloads_byte_identical':sum(e['gzip_byte_identical']for e in entries),'entries':entries,'scope':'Exact finite native coefficient reconstruction; no refutation search or unbounded semantic proof.'}
 (R/'COEFFICIENT_RECONSTRUCTION.json').write_text(json.dumps(certificate,indent=2)+'\n')
 return {'status':'PASS','raw_payloads_byte_identical':len(entries),'gzip_payloads_byte_identical':certificate['gzip_payloads_byte_identical'],'receipt':'COEFFICIENT_RECONSTRUCTION.json'}
def main():
 raw=json.loads((R/'laurent_candidate.json').read_text());T0=table(raw['majorant']);olddef=table(raw['defect'])
 A,C,i,t,D,J,e,F,L,G,H,I=expression_setup();rad=times(times(D,F),I)
 require(rad==table(raw['radicand']),'radical expansion')
 defect=plus(power(T0,2),scale(times(power(C,14),rad),2**32),-1)
 require(defect==olddef,'exact majorant defect')
 cert=json.loads((R/'laurent_cone_certificate.json').read_text());cone_counts={}
 for name,p in [('majorant',T0),('defect',defect)]:
  shifted=translate(p)
  require(shifted==table(cert[name]['coefficients']),'complete cone certificate '+name)
  require(all(v>0 for v in shifted.values()),'positive cone coefficients '+name)
  require(shifted.get((0,0,0,0),0)>0,'positive constant '+name);cone_counts[name]=len(shifted)
 # Independently reconstruct the old unpadded majorant to check the110-term rewrite.
 Ns=plus(scale(G,2),L);ee=power(e,2)
 N1=plus(scale(times(times(times(ee,D),plus(D,number(1),-1)),L),2),scale(C,3))
 N2=scale(times(times(ee,plus(D,number(1),-1)),L),2)
 N3=scale(times(ee,plus(L,C,-1)),2);N4=scale(times(ee,C),2)
 bracket=times(plus(plus(scale(power(D,2),2048),scale(D,-1024)),number(-256)),Ns)
 for p,k in [(N1,-128),(N2,-80),(N3,-56),(N4,-42)]:bracket=plus(bracket,scale(p,k))
 bracket=plus(bracket,times(power(i,2),plus(plus(number(1568),scale(A,-448)),scale(C,288))))
 oldcore=times(e,bracket)
 corrraw=json.loads((R/'laurent_correction_nopad_4JDbasis.json').read_text())
 Corr=expand_table(corrraw,[J,C,i,t,D])
 T=plus(scale(times(times(power(C,7),oldcore),H),64),Corr,-1)
 require(T==scale(T0,4),'exact compact majorant identity')
 # The literal new DAG is checked symbolically on its complete new portions.
 doc=json.loads((R/'laurent9_positive.json').read_text());n=doc['named_nodes']
 leaves={x['name']:k for k,x in enumerate(doc['nodes'])if x['kind']=='variable'}
 # Verify the guard parameter before treating it as an independent cut leaf.
 Rvar,Cvar,jvar=(var(k,3)for k in range(3))
 t_expected=plus(plus(scale(Rvar,2),number(1,3)),times(plus(jvar,number(1,3),-1),Cvar))
 t_cuts={n['R']:Rvar,n['C']:Cvar,leaves['j']:jvar}
 require(symbolic_dag(doc,n['Laurent_t'],t_cuts,3)==t_expected,'literal guard parameter t=2R+1+(j-1)C')
 cuts={n['A']:A,n['C']:C,leaves['i']:i,n['Laurent_t']:t,n['H']:H}
 require(symbolic_dag(doc,n['Laurent_T'],cuts,4)==T,'literal majorant DAG')
 S=scale(power(C,7),2**18);a1=times(power(S,2),rad)
 require(symbolic_dag(doc,n['Laurent_a1'],cuts,4)==a1,'literal scaled radical DAG')
 names=('E0','Omega','V0','Laurent_T','a0','Laurent_a1')
 vv=[var(j,6)for j in range(6)];outercuts={n[k]:vv[j]for j,k in enumerate(names)}
 Ee,Om,Vv,Tt,aa,bb=vv;th=plus(Ee,times(Om,plus(Vv,Tt)),-1)
 expected=plus(power(plus(power(th,2),times(power(Om,2),plus(aa,bb)),-1),2),scale(times(times(power(Om,4),aa),bb),4),-1)
 require(symbolic_dag(doc,doc['output'],outercuts,6)==expected,'literal outer norm identity')
 # Every inherited source/Pell register used by the proof is unchanged.
 basepath=R/'upstream/71-determinant-guards/nine_positive/generated/composed9_positive.json'
 require(hashlib.sha256(basepath.read_bytes()).hexdigest()=='f5d00f414abd0c61e1d7f11b682474f63bc34b08e44730de20a5829e2a613e25','pinned source DAG')
 base=json.loads(basepath.read_text())
 fixed_metadata=('coefficient_recipes','base_scale_exponent','threshold_scale_exponent','coefficient_bound_exponent','port_bit_lengths','coherent_tuple','source_sha256','layout_sha256','Kcode','W','threshold_B_power')
 for field in fixed_metadata:
  require(doc.get(field)==base[field],'fixed metadata preservation '+field)
 for name in ('R','N','A','P','K','V0','a0','Omega','E0','D','F','G','H','I'):
  require(canonical(base,base['named_nodes'][name])==canonical(doc,n[name]),'source preservation '+name)
 live=set();stack=[doc['output']]
 while stack:
  idx=stack.pop()
  if idx in live:continue
  live.add(idx);node=doc['nodes'][idx]
  if 'left'in node:stack.extend((node['left'],node['right']))
 require(len(live)==len(doc['nodes']),'DAG dead nodes')
 counts=dict(Counter(x['kind']for x in doc['nodes']if 'left'in x))
 require(counts=={'mul':430,'sub':31,'add':265}and sum(counts.values())==726,'exact operation count')
 lead=source_leaders(base)
 require({k:v['degree']for k,v in lead.items()}=={'R':7963,'N':2115,'A':16425,'K':28620,'V0':57239,'a0':114478,'Omega':82360,'E0':16429},'source degrees')
 weights=(16425,1,1,7963)
 def wd(p):return max(sum(a*b for a,b in zip(m,weights))for m in p)
 require(wd(T)==385774 and wd(defect)==377328,'new exact weighted degrees')
 top=[(m,c)for m,c in defect.items()if sum(a*b for a,b in zip(m,weights))==wd(defect)]
 require(top==[((22,42,10,2),141664530202624)],'unique defect leader')
 require(max(m[0]for m in defect)==22,'Laurent remainder order')
 o=82360;v0=57239;k=28620;tdeg=385774;d1=377328;bdeg=2*o+d1
 degrees=[2*bdeg,2*o+v0+tdeg+bdeg,4*o+2*k+2*tdeg,4*o+2*v0+d1]
 require(degrees==[1084096,1149781,1158228,821246],'norm exact-degree comparison')
 lc={name:table(value['leader'])for name,value in lead.items()}
 lct=scale(times(power(lc['A'],23),lc['R']),2**29)
 final_lc=scale(times(times(power(lc['Omega'],4),power(lc['K'],2)),power(lct,2)),4)
 require(final_lc=={(0,0,0,0,578828,276):2**166},'exact diagonal leading coefficient')
 binding=check_binding()
 reconstruction=reconstruct_coefficients()
 # A deliberately corrupted coefficient fails the full exact expansion.
 corrupted=dict(T0);key=next(iter(corrupted));corrupted[key]+=1
 require(plus(power(corrupted,2),scale(times(power(C,14),rad),2**32),-1)!=defect,'negative coefficient control')
 output={'status':'PASS','new_majorant_terms':len(T0),'compact_correction_terms':len(corrraw),'cone_terms':cone_counts,'operations':counts,'total_operations':726,'exact_degree':1158228,'norm_candidate_degrees':degrees,'diagonal_leading_coefficient':{'power_of_two':166,'base_scale_power':578828,'threshold_scale_power':276},'source_leaders':lead,'fixed_port_bits':binding,'coefficient_reconstruction':reconstruction,'guard_parameter_identity_checked':True,'fixed_metadata_matches_source':list(fixed_metadata),'scope':'Finite exact algebra and literal implementation; inherited native/Pell/refutation semantic theorems are not newly formalized.'}
 (R/'VERIFICATION.json').write_text(json.dumps(output,indent=2)+'\n');print(json.dumps(output))
if __name__=='__main__':main()
