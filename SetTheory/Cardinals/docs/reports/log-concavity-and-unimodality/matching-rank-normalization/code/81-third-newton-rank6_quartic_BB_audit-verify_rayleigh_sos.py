"""Standard-library SOS certificate for the shared Rayleigh slack on real cones."""
from verify_Rayleigh_repairs import R,add,mul,variable,translate,need,matching,TYPES,F,OUT
from itertools import combinations_with_replacement
import hashlib,json
D=add(mul(variable(2),variable(5)),mul(variable(1),variable(6)),F(-1))
remainder=add(R,mul(D,D),F(-6));records=[]
for basis in combinations_with_replacement(TYPES,2):
 if not matching(tuple(x&3 for x in basis),2):continue
 shifted=translate(remainder,basis)
 need(all(c>=0 for c in shifted.values()),('SOS remainder sign',basis))
 text=json.dumps([[list(e),str(c)] for e,c in sorted(shifted.items())],separators=(',',':'))
 records.append({'basis':basis,'nonzero_coefficients':len(shifted),'minimum':str(min(shifted.values(),default=0)),'sha256':hashlib.sha256(text.encode()).hexdigest()})
need(len(records)==15,'pair-cone count')
out={'all_pass':True,'identity':'12 K = 6 (N2 N5 - N1 N6)^2 + remainder','unshifted_Rayleigh_terms':len(R),'pair_cones':15,'nonnegative_remainder_coefficients':sum(v['nonzero_coefficients'] for v in records),'records':records}
(OUT/'rayleigh_sos_certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='records'},indent=2))
