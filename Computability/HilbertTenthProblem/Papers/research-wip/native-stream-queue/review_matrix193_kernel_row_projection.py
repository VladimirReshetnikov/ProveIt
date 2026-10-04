#!/usr/bin/env python3
"""Independent pinned-data audit of the full kernel-row193 recoding."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

AUTHOR = {
 'matrix193_kernel_row_projection.py': '2eb89dfae4e9352fa67c707109853c025c823ab34869bc25f54912736734d105',
 'matrix193_kernel_row_projection.json': '543d461a50bc1bb31c1e8bcc60ede58a5e9815b194ddd49c5640e3a50611caeb',
 'matrix193_kernel_row_projection.md': '400aab15caa9462808cc2dc2ef68f013797a9bc656c97acecdd610de81a13c6e',
}
PINS = {
 'group_directed_semigroup193.json': 'c802f1ca0fde3cfcc856dd0f14ea2bf6270e1a9a924fe9743ee00c4336891639',
 'group_directed_semigroup193.md': '75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e',
 'matrix193_schreier_recode.json': 'e2a01632a9689aaf9ef5966b9f92772b59d71cd4d392d46346ebc890aa8dc9ea',
 'matrix193_schreier_recode.md': '17d67b09b8c05a453be7f23b66a3582fd90c776d57d6e32979b78425bd904f55',
 'u15_unary_block_interface.json': 'a08e400d61ae5df0a25916f899d7e1e9e0225bc1d1d40052d4dc89ed435c30a0',
 'u15_unary_block_interface.md': 'cdc686700af3545609796034e0a2c906bd0438b6bcabc0c0b267954cc9d20452',
}
I = (1, 0, 0, 1)
P = (1, 2, 0, 1)

def need(ok, message):
 if not ok: raise ValueError(message)

def digest(raw): return hashlib.sha256(raw).hexdigest()

def pairs(items):
 result = {}
 for k, v in items:
  need(k not in result, 'duplicate key'); result[k] = v
 return result

def bad_float(value): raise ValueError('nonfinite JSON ' + value)

def read(path): return json.loads(path.read_text(), object_pairs_hook=pairs, parse_constant=bad_float)

def exact(a, b):
 if type(a) is not type(b): return False
 if isinstance(a, dict): return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
 if isinstance(a, list): return len(a) == len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a == b

def mm(a,b):
 x,y,z,t=a; u,v,w,s=b
 return x*u+y*w, x*v+y*s, z*u+t*w, z*v+t*s

def inverse(a):
 x,y,z,t=a; need(x*t-y*z==1, 'SL2 inverse'); return t,-y,-z,x

def pow2(a,n):
 if n<0: a=inverse(a); n=-n
 out=I
 while n:
  if n%2: out=mm(out,a)
  a=mm(a,a); n//=2
 return out

def ej(j): return 1+4*j, 2, -8*j*j, 1-4*j

def flatten(a): return tuple(z for row in a for z in row)
def rows(a): return [list(a[:2]),list(a[2:])]
def diag(a,b): return [list(a[:2])+[0,0],list(a[2:])+[0,0],[0,0]+list(b[:2]),[0,0]+list(b[2:])]

def word(w,codes):
 out=I
 for c in w: out=mm(out,codes[c])
 return out

def full_array(parent,codes):
 out=[]
 for kind in ('A','B'):
  for tile in parent['tiles']:
   upper=word(tile['h' if kind=='A' else 'g'],codes)
   lower=ej(tile['id'])
   if kind=='B': upper=inverse(upper); lower=mm(mm(inverse(P),inverse(lower)),P)
   out.append({'name':kind+str(tile['id']), 'tile_id':tile['id'], 'matrix':diag(upper,lower)})
 out.append({'name':'C','tile_id':None,'matrix':diag(inverse(word('[J1]#',codes)),P)})
 return out

def stats(array):
 values=[v for record in array for row in record['matrix'] for v in row]
 return {'generators':len(array),'entry_slots':len(values),'nonzero_entries':sum(v!=0 for v in values),'maximum_absolute_entry':max(map(abs,values)),'maximum_magnitude_bits':max(abs(v).bit_length() for v in values),'sum_magnitude_bits':sum(abs(v).bit_length() for v in values)}

def verify(root,author_root):
 for name,pin in PINS.items(): need(digest((root/name).read_bytes())==pin,'dependency '+name)
 for name,pin in AUTHOR.items(): need(digest((author_root/name).read_bytes())==pin,'author '+name)
 receipt=read(author_root/'matrix193_kernel_row_projection.json')
 need(receipt['source_sha256']==AUTHOR['matrix193_kernel_row_projection.py'],'author self source')
 need(exact(receipt['pins'],PINS),'author dependency inventory')
 old_receipt=read(root/'group_directed_semigroup193.json'); old=old_receipt['packet']; new=receipt['packet']
 letters=['0','1']+list('ABCDEFGHIJKLMNO')+['[',']','#']
 need(old['alphabet']+['#']==letters,'alphabet')
 codes=dict(zip(letters,[mm(ej(0),inverse(ej(1))),ej(1)]+[ej(j) for j in range(2,20)]))
 need(mm(codes['0'],codes['1'])==P,'Nielsen inverse')
 need(exact({k:rows(v) for k,v in codes.items()},new['top_matrices']),'all twenty codes')
 for key in ('alphabet','separator','terminal','tiles','rules','deleted_old_tile_ids'): need(exact(old[key],new[key]),'unchanged '+key)
 expected_words={'0':[1,-2,-1,2],'1':[-2,1,2]}
 expected_words.update({a:[-2]*j+[1]+[2]*j for j,a in enumerate(letters) if j>=2})
 need(exact(expected_words,new['top_words_in_PQ']),'ambient basis words')
 for w in expected_words.values(): need(sum((v==2)-(v==-2) for v in w)==0,'Q exponent')
 old_codes={a:ej(j) for a,j in old['top_codes'].items()}
 rebuilt_old=full_array(old,old_codes); rebuilt=full_array(old,codes)
 need(exact(rebuilt_old,old['generators']),'all old entries')
 need(exact(rebuilt,new['generators']),'all new entries')
 need(exact(stats(rebuilt),receipt['new_statistics']) and exact(stats(rebuilt),new['ledger']),'new statistics')
 need(exact(stats(rebuilt_old),receipt['old_statistics']),'old statistics')
 schreier=read(root/'matrix193_schreier_recode.json')['packet']['generators']
 need(exact(stats(schreier),receipt['schreier1057_statistics']),'Schreier statistics')
 need(len({tuple(flatten(g['matrix'])) for g in rebuilt})==193,'distinct generators')
 for a,b in zip(rebuilt_old,rebuilt):
  need(a['matrix'][2:]==b['matrix'][2:],'lower blocks unchanged')
  m=b['matrix']
  for z in (flatten([r[:2] for r in m[:2]]),flatten([r[2:] for r in m[2:]])):
   need(z[0]*z[3]-z[1]*z[2]==1 and tuple(v%2 for v in z)==I,'Gamma2 SL2 blocks')
 witness=old_receipt['accepting_witness']; by_name={g['name']:g['matrix'] for g in rebuilt}
 upper=lower=I
 for name in witness['generator_word']:
  mat=by_name[name]; upper=mm(upper,flatten([r[:2] for r in mat[:2]])); lower=mm(lower,flatten([r[2:] for r in mat[2:]]))
 target_upper=inverse(word(witness['input']['configuration_word']+'#',codes))
 need(len(witness['generator_word'])==167 and (upper,lower)==(target_upper,P),'complete accepted product')
 need(exact(diag(upper,lower),receipt['accepting_witness']['product']) and exact(diag(upper,lower),receipt['accepting_witness']['target']),'saved product')
 need(exact(receipt['accepting_witness']['generator_word'],witness['generator_word']),'saved generator word')
 W=word('01010111',codes); need(W==(-87,-38,-16,-7),'physical W')
 B=mm(W,W); a0=(B[0]+B[3])//2; delta=a0*a0-1; D=(B[0]-a0,B[1],B[2],B[3]-a0)
 need(a0==4417 and mm(D,D)==(delta,0,0,delta),'Pell parameter and algebra')
 need(exact(rows(W),receipt['block']['matrix']) and exact(rows(B),receipt['block']['square']) and exact(rows(D),receipt['block']['D']),'saved power matrices')
 expected_source=[['cu11','*','chi','c11'],['dv11','*','psi','d11'],['target11','-','cu11','dv11'],['cu12','*','chi','c12'],['dv12','*','psi','d12'],['target12','-','cu12','dv12']]
 src=receipt['target_assembly']['source']; need(exact(src,expected_source),'literal six-row source')
 coeffs={'chi':{('chi',):1},'psi':{('psi',):1}}
 for k in ('c11','c12','d11','d12'): coeffs[k]={(k,):1}
 for n,op,a,b in src:
  if op=='*': coeffs[n]={tuple(sorted(x+y)):vx*vy for x,vx in coeffs[a].items() for y,vy in coeffs[b].items()}
  else:
   coeffs[n]=dict(coeffs[a])
   for key,value in coeffs[b].items(): coeffs[n][key]=coeffs[n].get(key,0)-value
 for label in ('11','12'): need(coeffs['target'+label]=={tuple(sorted(('chi','c'+label))):1,tuple(sorted(('psi','d'+label))):-1},'coefficient identity')
 pending=['target11','target12']; live=set(); deps={n:(a,b) for n,op,a,b in src}
 while pending:
  n=pending.pop()
  if n not in live: live.add(n); pending.extend(deps.get(n,()))
 need(live==set(coeffs),'all ports and operations live')
 contexts=['','0','1','A','[',']','#','01','[A0','10]']; chi,psi=1,0; checked=0
 for x in range(13):
  power=pow2(B,-x); need(power==tuple(chi*z-psi*d for z,d in zip(I,D)),'independent binary power')
  need(exact(receipt['block']['checked_powers'][x],{'x':x,'chi':chi,'psi':psi,'negative_power':rows(power)}),'saved Pell pair')
  for u,v in itertools.product(contexts,repeat=2):
   L=inverse(word(v+'#',codes)); R=inverse(word(u,codes)); C=mm(L,R); F=mm(mm(L,D),R)
   env={'chi':chi,'psi':psi,'c11':C[0],'c12':C[1],'d11':F[0],'d12':F[1]}
   for n,op,a,b in src: env[n]=env[a]*env[b] if op=='*' else env[a]-env[b]
   target=inverse(word(u+'01010111'*(2*x)+v+'#',codes))
   need((env['target11'],env['target12'])==target[:2] and target==mm(mm(L,power),R),'complete context target')
   checked+=1
  chi,psi=a0*chi+delta*psi,chi+a0*psi
 need(receipt['new_universal_Diophantine_bound'] is False,'scope')
 return {'status':'PASS','source_sha256':digest(Path(__file__).read_bytes()),'author_pins':AUTHOR,'dependency_pins':PINS,'independent_checks':{'old_entries':3088,'new_entries':3088,'letters':20,'unchanged_lower_blocks':193,'accepted_product_length':167,'exact_Pell_powers':13,'literal_context_targets':checked,'source_gates':6,'symbolic_output_terms':4},'new_statistics':stats(rebuilt),'Pell_parameter':a0,'target_assembly':{'M':4,'A':2,'total':6},'scope':'Full finite matrix/source audit and separate mathematical proof read; inherited U15 reduction not reproved; no universal arithmetic bound.'}

def main():
 p=argparse.ArgumentParser(description=__doc__); p.add_argument('--root',type=Path,required=True); p.add_argument('--author-root',type=Path)
 g=p.add_mutually_exclusive_group(required=True); g.add_argument('--expect',type=Path); g.add_argument('--output',type=Path); args=p.parse_args()
 result=verify(args.root.resolve(),(args.author_root or args.root).resolve())
 if args.expect: need(exact(result,read(args.expect)),'exact receipt')
 else: args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'status':'PASS','checks':result['independent_checks'],'ledger':result['new_statistics']},sort_keys=True))
if __name__=='__main__': main()
