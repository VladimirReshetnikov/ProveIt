from pathlib import Path
import json,sys
from circuit import Circuit
ROOT=Path(__file__).resolve().parent
OLD=ROOT/'source'
def build(mode):
 old=json.loads((OLD/'integer10_polar.json').read_text());d=Circuit();ids=[]; oldnames={v:k for k,v in old['named_nodes'].items()}; reg_old=old['named_nodes']
 def rr(name):return ids[reg_old[name]]
 for index,n in enumerate(old['nodes']):
  kind=n['kind']
  if kind=='literal':v=d.c(n['value'])
  elif kind in ('variable','fixed'):v=d.leaf(kind,name=n['name'])
  else:v=d.op(kind,ids[n['left']],ids[n['right']])
  if index==reg_old['X']:
   xp1=d.sub(d.mul(rr('nn'),d.sub(d.add(rr('sc'),rr('tc_original')),d.c(1))),rr('sc'))
   v=d.sub(xp1,d.c(1))
  elif index==reg_old['K']:
   v=d.add(xp1,d.mul(rr('twice_k'),d.sub(rr('Phalf'),d.c(1))))
  elif index==reg_old['G']:v=d.sub(d.mul(rr('halfA'),rr('Fm1')),rr('F'))
  elif index==reg_old['I'] and mode in ('linear','cubic'):
   GH=d.mul(rr('G'),rr('H'));v=d.add(d.sub(d.mul(GH,GH),d.mul(rr('H'),rr('H'))),d.c(1))
  ids.append(v)
 reg={k:ids[v]for k,v in old['named_nodes'].items()}
 for k,v in reg.items():d.save(k,v)
 var={n['name']:ids[i]for i,n in enumerate(old['nodes'])if n['kind']=='variable'}
 A,M,S,P,c,N=d.add,d.mul,d.sub,d.pow,d.c,d.save
 h,aa,C,xi,G,H=[reg[n]for n in ['halfA','A','C','xi','G','H']]
 ss=reg['S'];s2=M(ss,ss);s3=M(ss,s2);sigma=N('Sigma_new',M(xi,s2,s3));rho=reg['rho'];rho2=M(rho,rho)
 theta=N('Theta_new',M(S(M(rho,S(rho2,s2)),s3),A(rho2,M(c(23),s2))))
 C2=P(C,2)
 if mode=='polar':R=c(0)
 elif mode=='linear':R=M(c(2),aa,reg['E'],GH)
 elif mode=='cubic':R=M(c(2),aa,reg['E0'],S(reg['D'],M(c(2),C2)),GH)
 elif mode=='sixterm':
  h2=P(h,2);u=C2
  a=A(M(u,S(M(c(2),h2),c(11))),c(6))
  b=A(S(M(c(8),P(h2,2)),M(c(52),h2)),c(143))
  b=A(M(P(u,2),b),M(u,S(M(c(32),h2),c(176))),c(48))
  J=S(reg['B1'],C)
  T=A(M(xi,J,a),M(c(16),reg['E0'],xi,var['y'],b),M(c(3),var['y']))
  R=M(c(32768),P(u,3),P(reg["E0"],4),P(h,9),S(M(S(h,c(1)),T),M(c(2),var['y'])))
 else:raise ValueError(mode)
 N('shear',R)
 Z=N('shifted_center',S(M(sigma,A(var['m'],R)),theta));sigma2=P(sigma,2);Z2=P(Z,2)
 inn=A(Z2,M(sigma2,S(reg['guard'],reg['lucas'])))
 out=S(P(inn,2),M(c(4),sigma2,reg['guard'],Z2));body=d.finish(out)
 body.update(schema='round13-exact-norm-sharing-v1', domain='Z',variables=old['variables'],fixed_recipes=old['fixed_recipes'],mode=mode,exact_degree={'polar':1245324,'linear':1179788,'cubic':1114252,'sixterm':1080888}[mode], fixed_coefficients='FIXED_COEFFICIENTS.json', proof='PROOF.md', polynomial_identity='Exactly the same polynomial as the corresponding pinned short-guard parent; local ring rewrites only.', count_convention='Each live binary addition, subtraction, multiplication including scalar products costs one; leaves and sharing are free.')
 (ROOT/f'integer10_{mode}.json').write_text(json.dumps(body,separators=(',',':'))+'\n')
 print(mode,body['total_operations'],body['degree_upper_bound'])
 return body
if __name__=='__main__':
 for mode in ['polar','linear','cubic','sixterm']:build(mode)
