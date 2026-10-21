#!/usr/bin/env python3
"""Independent literal blank replay, dense presentation, saved-case audit.

Does not import the inherited runtime checker or the construction wrapper.
This finite audit is complementary to, not a replacement for, symbolic proof.
"""
import argparse,gzip,hashlib,json
from pathlib import Path

def read(raw):
 start=None;table={}
 for line in raw.decode().splitlines():
  if line.startswith('#! start '):start=int(line.split()[-1]);continue
  if not line or line.startswith('#'):continue
  a,b,w,d,c=line.split();key=(int(a),int(b))
  assert key not in table and d in('R','L')
  table[key]=(int(w),1 if d=='R'else-1,int(c))
 assert start is not None
 return start,table

def digest(raw):return hashlib.sha256(raw).hexdigest()

def main():
 ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path);a=ap.parse_args();p=a.directory
 native=(p/'z215.native.tm').read_bytes();start,T=read(native)
 states=sorted({q for q,b in T});assert len(states)==215 and start==74
 assert{(q,b)for q in states for b in(0,1)}==set(T)
 order=[start]+[q for q in states if q!=start];mapping={q:i for i,q in enumerate(order)};mapping[254]=215
 dense=('#! start 0\n'+''.join(f'{mapping[q]} {b} {w} {"R"if d==1 else"L"} {mapping[z]}\n'for q in order for b in(0,1)for w,d,z in[T[q,b]])).encode()
 dstart,D=read(dense);assert dstart==0
 assert all(D[mapping[q],b]==(w,d,mapping[z])for(q,b),(w,d,z)in T.items())
 (p/'z215.tm').write_bytes(dense)
 (p/'canonicalization.json').write_text(json.dumps({'native_start':74,'dense_start':0,'native_dispatcher':84,'dense_dispatcher':mapping[84],'native_halt':254,'dense_halt':215,'native_to_dense':mapping,'dense_to_native':{v:k for k,v in mapping.items()},'native_sha256':digest(native),'dense_sha256':digest(dense)},indent=2)+'\n')
 st=json.loads(gzip.decompress((p/'startup.json.gz').read_bytes()));trace=st['trace']
 assert len(trace)==st['steps']==117004
 q=start;h=0;ones=set();dq=0;dh=0;dones=set();used=set()
 for expected in trace:
  r=int(h in ones);w,d,n=T[q,r];assert expected==[q,h,r,w,d,n];used.add((q,r))
  dr=int(dh in dones);dw,dd,dn=D[dq,dr]
  assert(dq,dh,dr,dw,dd,dn)==(mapping[q],h,r,w,d,mapping[n])
  if w:ones.add(h)
  else:ones.discard(h)
  if dw:dones.add(dh)
  else:dones.discard(dh)
  q=n;h+=d;dq=dn;dh+=dd
 assert(q,h)==(84,-4)and(dq,dh)==(mapping[84],-4)and ones==dones==set(st['one_cells'])
 values=st['physical_registers']+st['spares'];assert len(values)==76 and len(st['spares'])==67
 assert st['physical_registers']==[5,0,0,0,0,0,1,0,0]
 assert all(type(x)is int and x>=0 for x in values)
 expected_ones={-5,80};head=81
 for x in values:
  assert head not in expected_ones
  expected_ones.update(range(head+1,head+x+2));head+=x+2
 assert ones==expected_ones and st['header']==80 and st['gap']==20
 sites=json.loads((p/'sites215.json').read_bytes());cases=json.loads(gzip.decompress((p/'runtime_cases.json.gz').read_bytes()));report=json.loads((p/'runtime.json').read_bytes())
 expected_order=[(i,b)for i,(_,op,_)in enumerate(sites)for b in((False,True)if op=='CD'else(False,))]
 assert[(c['site_index'],c['positive'])for c in cases]==expected_order and len(cases)==6176
 assert report['status']=='UNIVERSAL_MATHEMATICAL_PASS'and report['expected_cases']==report['proved_cases']==6176 and not report['failures']
 assert report['table_sha256']==digest(native)and report['source_sha256']==digest((p/'sites215.json').read_bytes())
 assert report['append_value']==0 and report['start']==74
 assert all(len(c['duration'])==13 and all(type(x)is int and x>=0 for x in c['duration'])and c['duration'][0]>0 for c in cases)
 assert sum(c['symbolic_steps']for c in cases)==report['symbolic_steps']==1698790
 assert set(map(tuple,report['native_rows_covered_including_blocks']))==set(T)
 summary={'status':'PASS','scope':'Independent full literal replay of both presentations; exact complete terminal tape; all ordered saved cases and positive affine durations. Does not independently rederive symbolic induction rules.',
  'native_sha256':digest(native),'dense_sha256':digest(dense),'reviewer_sha256':digest(Path(__file__).read_bytes()),
  'startup_steps':len(trace),'native_start':start,'dense_start':dstart,'native_dispatcher':q,'dense_dispatcher':dq,'head':h,'header':80,'gap':20,'registers':[1,0,5,0,0,0,0,0,0],
  'spare_count':67,'one_cell_count':len(ones),'minimum_one':min(ones),'maximum_one':max(ones),
  'complete_zero_exterior':True,'rows_covered_in_symbolic_proof':len(T),'ordered_cases':len(cases),
  'minimum_duration_constant':min(c['duration'][0]for c in cases),'native_startup_rows_used':len(used)}
 (p/'independent_review.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
