#!/usr/bin/env python3
"""Finite source/pool binding, independent of the emitting programs.
Unbounded signed-Pell and arithmetic conclusions are proved in COMPOSITION_PROOF.md.
"""
import json,hashlib,copy,sys,importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('polycheck',ROOT/'inherited/verify_pooling_original.py');p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
add,mul,neg,scale,sq,sub,lin=p.summation,p.times,p.negative,p.scalar,p.square,p.difference,p.lin
parse=p.parsed

def read(f):return json.loads(f.read_bytes())
def enc(a):return(json.dumps(a,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(a):return hashlib.sha256(enc(a)).hexdigest()
def check(b,msg):
 if not b:raise ValueError(msg)
def audit(anchorname,variant):
 count=0
 def ck(b,msg):
  nonlocal count
  check(b,msg);count+=1
 n0=int(anchorname[-3:]);origbase=ROOT/'upstream173/source'/('anchor'+str(n0));original=read(origbase/'equation.json');ac=read(origbase/'certificate.json');ren=dict(ac['original_to_final'])
 def ov(i,c=1):return lin((c,ren[i]))
 base=ROOT/'sources'/anchorname;parent=read(base/'signed_anchor_parent.json');expected=copy.deepcopy(original)
 tmin=128 if n0==221 else 16;vi=next(i for i,v in enumerate(expected['variables']) if v['name']=='cofinal.horizon_root');ri=next(i for i,r in enumerate(expected['residuals']) if r['label']=='cofinal.horizon')
 expected['residuals'][ri]['terms']=[[c,list(m)] for m,c in sorted(add(ov(0),lin((-2*tmin,vi),(-tmin,None))).items())]
 expected['variables'][vi]['name']='cofinal.horizon_parameter';expected['schema']='conzfc-signed-cofinal-anchor-v1';expected['semantic_transform']='t = tmin*(2*z+1); positivity recovered from powers'
 ck(parent==expected,'Signed horizon changed other source data')
 rows=[parse(r['terms'],n0) for r in parent['residuals']];labels=[r['label'] for r in parent['residuals']]
 A=add(ov(142),lin((1,None)));K=ov(100) if n0==221 else scale(1<<20,ov(0))
 # Explicit authentic power requests, including all affine coordinate offsets.
 requests=[(0,ov(0),K,ov(2),ov(191),ov(192),ov(193)),
  (1,ov(4),ov(1),ov(18),ov(182),ov(183),add(ov(184),lin((1,None)))),
  (2,ov(194),ov(1),add(ov(102),lin((-1,None))),ov(182),ov(183),add(ov(184),lin((1,None))))]
 q=add(ov(102),lin((-1,None)));qp=ov(102)
 qm=[(104,146,147,148,ov(0),0,0),(121,173,174,175,ov(5),0,0),(128,182,183,184,ov(1),0,1)]
 pm=[(103,155,156,157,add(ov(0),ov(2)),0,0),(108,158,159,160,add(ov(9),lin((-1,None))),-1,0),
 (111,161,162,163,ov(10),0,0),(114,164,165,166,ov(11),0,0),(117,167,168,169,ov(12),0,0),
 (120,170,171,172,ov(13),0,0),(124,176,177,178,ov(14),0,0),(127,179,180,181,ov(15),0,0),
 (132,185,186,187,ov(16),0,0),(135,188,189,190,scale(2,ov(17)),0,0)]
 for gj,n,members in [(3,q,qm),(4,qp,pm)]:
  for mi,di,yi,zi,k,yo,zo in members:requests.append((gj,n,k,ov(mi),ov(di),add(ov(yi),lin((yo,None))),add(ov(zi),lin((zo,None)))))
 ck(len(requests)==16,'Request count')
 unique={}
 for gj,n,k,m,D,Y,Z in requests:
  gate=sub(Z,mul(A,Y));norm=add(sq(D),scale(2,mul(D,Z)),sq(Y),lin((-1,None)))
  ck(gate in rows,'Missing actual AY gate');ck(norm in rows,'Missing actual norm')
  key=digest([[c,list(mm)] for mm,c in sorted(D.items())]);unique[key]=(k,D,Y,Z,norm)
 ck(len(unique)==14,'Distinct canonical-pair count')
 orientation={}
 for k,D,Y,Z,norm in unique.values():orientation=add(orientation,sq(add(D,Z,lin((-1,None)))),sq(sub(Y,k)),neg(norm))
 orientation=add(orientation,neg(mul(sub(A,lin((1,None))),ov(209))))
 # Parent225 Q=209; it maps to anchor's pooled quotient.
 ck(orientation==rows[labels.index('cap.pooled_index_residue')],'Actual signed-index orientation row')
 atoms=[parse(a['terms']) for a in ac['frame_atoms_before_renumbering']]
 def oldmap(f):return {tuple(sorted(ren[i] for i in m)):c for m,c in f.items()}
 atoms=[oldmap(a) for a in atoms]
 frame=add(ov(141),lin((-2,None)),*[neg(sq(a)) for a in atoms])
 ck(frame==rows[labels.index('shared.frame_definition')],'Squared frame complete')
 for gj,n,k,m,D,Y,Z in requests:
  ck(n in atoms and k in atoms and m in atoms,'Every actual power atom is framed')
 e=read(base/variant/'equation.json');c=read(base/variant/'certificate.json');met=read(base/variant/'metrics.json')
 ck(c['parent_canonical_sha256']==digest(parent)==e['parent_equation_sha256'],'New parent hash')
 ck(c['parent_byte_sha256']==hashlib.sha256((origbase/'equation.json').read_bytes()).hexdigest(),'Inherited parent byte hash')
 ck(c['equation_sha256']==digest(e),'Pool equation hash')
 gone=[ren[i] for i in (149,150,151,152,153,154,221,222,223,224)];gone.sort()
 gone_rows=[i for i,r in enumerate(rows) if any(any(v in m for v in gone) for m in r)]
 ck(c['removed_variables']==gone and c['removed_rows']==gone_rows,'Private-coordinate deletion list')
 keep=[i for i in range(n0) if i not in gone];nr={i:j for j,i in enumerate(keep)}
 def remap(f):return {tuple(sorted(nr[i] for i in m)):v for m,v in f.items()}
 ck(c['retained_old_indices']==keep,'Retained index map')
 ck(e['variables'][:len(keep)]==[parent['variables'][i] for i in keep],'Retained names')
 rr=[i for i in range(len(rows)) if i not in gone_rows]
 ck(len(e['residuals'])==len(rr)+len(c['blocks']),'Exact row partition')
 for j,i in enumerate(rr):ck(parse(e['residuals'][j]['terms'])==remap(rows[i]),'Retained row changed')
 for gj in range(5):
  reqs=[r for r in requests if r[0]==gj];n=reqs[0][1];T=add(scale(2,mul(A,n)),neg(sq(n)),lin((-1,None)));E={}
  for _,_,k,m,D,Y,Z in reqs:E=add(E,sq(sub(m,D)),neg(sq(Y)),scale(-2,mul(n,Y,add(m,neg(D),neg(Z)))))
  g=c['groups'][gj]
  for field,f in [('base',n),('T',T),('E',E)]:ck(parse(g[field])==remap(f),'Actual request pool '+field)
  if gj<3:
   _,_,k,m,D,Y,Z=reqs[0];delta=add(m,neg(D),neg(mul(n,Y)));tv,qv=ren[149+2*gj],ren[150+2*gj]
   expectedT=sub(lin((1,tv)),T);ck(expectedT in rows or neg(expectedT) in rows,'Original modulus row')
   ck(add(delta,mul(lin((1,tv)),lin((1,qv)))) in rows,'Original quotient row')
   ck(parse(g['delta'])==remap(delta),'Singleton delta')
  else:
   prefix='radix' if gj==3 else 'radix_plus_one';ar=rows[labels.index(prefix+'.bilinear_aggregate')];br=rows[labels.index(prefix+'.pooled_norm')];Lv=ren[224 if gj==3 else 222]
   ck(sub(E,mul(T,lin((1,Lv))))==add(br,mul(n,ar)),'Original pooled restoration identity')
 for j,block in enumerate(c['blocks']):
  ids=block['groups'];Ts=[parse(c['groups'][i]['T']) for i in ids];z=lin((1,block['quotient_index']))
  if block['weights']=='direct':result=add(parse(c['groups'][ids[0]]['delta']),mul(z,Ts[0]))
  else:
   result=neg(mul(z,*Ts))
   for at,gidx in enumerate(ids):
    g=c['groups'][gidx];weight=parse(g['base']) if block['weights']=='base' else lin((1,None));result=add(result,mul(weight,parse(g['E']),*[T for k,T in enumerate(Ts) if k!=at]))
  ck(result==parse(e['residuals'][len(rr)+j]['terms']),'Final pooled residual')
 ck(met['degree']==2*max(len(m) for r in e['residuals'] for c,m in r['terms']),'Literal source degree')
 return {'status':'PASS','anchor':anchorname,'variant':variant,'checks':count,'request_count':len(requests),'canonical_pairs':len(unique),'source_sha256':digest(e),'equation_metrics':met}
if __name__=='__main__':
 results=[]
 for anchor in ['linear219','linear221']:
  for variant in ['all5','staged','paired']:results.append(audit(anchor,variant));print(anchor,variant,'PASS',flush=True)
 (ROOT/'verification').mkdir(exist_ok=True);(ROOT/'verification/composition.json').write_text(json.dumps({'status':'PASS','results':results},sort_keys=True,indent=2)+'\n')
