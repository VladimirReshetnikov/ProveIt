#!/usr/bin/env python3
"""Certificate serializer; optimizer output and selective source are inert data."""
import copy,hashlib,json,math,pathlib,sys
import sympy as sp
ROOT=pathlib.Path(__file__).resolve().parent
SOURCE=ROOT/'data/selective12_source.json'
base=json.loads(SOURCE.read_text())
SYMBOLS={n:sp.Symbol(n) for n in base['variables']+base['ports']}
def emit(tag,positions,targets):
 c,*w=positions;W=max(positions)
 out={k:copy.deepcopy(base[k]) for k in ['variables','ports','shifted_coordinates','coordinate_map','rows']}
 out.update(schema='round8-signed-selective-active-isolation-v1',construction='Selective-positive source, active-only pair isolation, signed overlapping target placement',source_file='data/source_system60.json',source_sha256=base['source_sha256'],source_variant='selective12',source_variant_file='data/selective12_source.json',source_variant_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),padding_exponent=c,weights=w,maximum_weight=W,target_exponents=targets,target_maximum=max(targets),coefficient_signs=[1]*22)
 allterms=[]
 for row,H in zip(out['rows'],targets):
  row['target_exponent']=H
  for t in row['terms']:
   a=t['alpha'];t['weight']=(2-sum(a))*c+sum(x*y for x,y in zip(a,w));t['encoding_exponent']=H-t['weight'];assert t['encoding_exponent']>=0
   t['multinomial_inverse_weight']=math.factorial(2-sum(a))*math.prod(math.factorial(x) for x in a)
   allterms.append((row,t))
 leadrow,lead=max(allterms,key=lambda rt:rt[1]['encoding_exponent'])
 leadval=int(lead['weighted_coefficient']);assert leadval
 if leadval<0:
  j=leadrow['original_row_one_based']-1;out['coefficient_signs'][j]=-1
  leadrow['polynomial']=str(-sp.sympify(leadrow['polynomial'],locals=SYMBOLS))
  for t in leadrow['terms']:
   for key in ['coefficient','weighted_coefficient']:t[key]=str(sp.expand(-sp.sympify(t[key],locals=SYMBOLS)))
 out.update(Dmax=lead['encoding_exponent'],Kcode=lead['encoding_exponent']+2*W,leading_encoded_coefficient=abs(leadval),leading_row_one_based=leadrow['original_row_one_based'],source_record_count=len(allterms),active_monomial_count=len({tuple(t['alpha']) for r,t in allterms}))
 out['sparse_padding_headroom']=out['Kcode']-out['target_maximum'];assert out['sparse_padding_headroom']>=2
 dest=ROOT/f'CERTIFICATE_{W}_selective12_{tag}.json';dest.write_text(json.dumps(out,indent=2)+'\n')
 print(dest.name,'Dmax',out['Dmax'],'Kcode',out['Kcode'],'padding',c,'lead',out['leading_encoded_coefficient'],'signs',out['coefficient_signs'])
 return dest
if __name__=='__main__':
 for arg in sys.argv[1:]:
  lines=(ROOT/arg).read_text().splitlines();d,W=map(int,lines[0].split());positions=list(map(int,lines[1].split()));targets=list(map(int,lines[2].split()));assert max(positions)==W
  emit('packed',positions,targets)
  shift=max(0,2*W-min(targets));emit('packed_shifted',positions,[h+shift for h in targets])
  emit('regular',positions,[(j+1)*(2*W+1) for j in range(22)])
