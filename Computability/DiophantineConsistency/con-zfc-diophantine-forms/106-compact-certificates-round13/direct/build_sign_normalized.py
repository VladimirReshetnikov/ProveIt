#!/usr/bin/env python3
"""Existential sign normalization for the frozen parametric integer template.
Only U and Z in each Pell graph are normalized; all sign actions receive
complete exact residual-parity certificates. Does not alter frozen outputs.
"""
import argparse,collections,hashlib,json,pathlib
import build_integer as integer
ROOT=pathlib.Path(__file__).resolve().parent

def must(x,m):
 if not x:raise ValueError(m)
def parity(mon,flips):return sum(i in flips for i in mon)%2

def main():
 p=argparse.ArgumentParser();p.add_argument('--source',type=pathlib.Path,default=ROOT/'parametric_signed_template');p.add_argument('--prior-integer',type=pathlib.Path,default=ROOT/'parametric_integer');p.add_argument('--output',type=pathlib.Path,default=ROOT/'normalized_integer');args=p.parse_args()
 raw=json.loads((args.source/'circuit.json').read_text());eq=json.loads((args.source/'equation.json').read_text());aff=json.loads((args.source/'affine_restoration.json').read_text());cert=json.loads((args.prior_integer/'sign_certificate.json').read_text());name={v['name']:i for i,v in enumerate(raw['variables'])};mapping={int(k):v for k,v in aff['old_to_new'].items()};free=set(raw['bindings']['unrestricted_integer_quotients']);seeds=set(cert['raw_seed_indices']);actions=[];pivots=set()
 for macro in raw['macros']:
  if macro['kind']!='power':continue
  tag=macro['tag']
  for target in ['U','Z']:
   pivot=name[tag+'.'+target];pivots.add(pivot);flips={pivot}
   if target=='U':flips|={name[tag+'.B_mod_U.quotient'],name[tag+'.S_mod_U.quotient']}
   for row in raw['residuals']:
    gate=row['gate']
    if gate is None:continue
    rhs=[m for c,m in row['terms'] if m!=[gate]];ps={parity(m,flips) for m in rhs};must(len(ps)<=1,'non-diagonal gate action')
    if ps=={1}:flips.add(gate)
   raw_parities=[]
   for row in raw['residuals']:
    ps={parity(m,flips) for c,m in row['terms']};must(len(ps)<=1,'raw row parity disagreement');raw_parities.append(next(iter(ps),0))
   other_semantics={i for i in flips if raw['variables'][i]['kind']!='gate' and i not in free};must(other_semantics=={pivot},'action touches another semantic coordinate')
   exported={mapping[i] for i in flips if i in mapping};exported_parities=[]
   for row in eq['residuals']:
    ps={parity(m,exported) for c,m in row['terms']};must(len(ps)<=1,'exported row parity disagreement');exported_parities.append(next(iter(ps),0))
   actions.append({'pivot':pivot,'name':tag+'.'+target,'raw_flips':sorted(flips),'exported_flips':sorted(exported),'raw_row_parities':raw_parities,'exported_row_parities':exported_parities})
 must(pivots<=seeds,'some sign pivots not guarded in frozen predecessor')
 guards=seeds-pivots;required=set(cert['required_semantic_variables']);known,proof=integer.closure(guards|pivots,cert['rules']);must(required<=known,'sign closure failed')
 for a in actions:must(not(set(a['raw_flips'])&guards),'action changes retained guard')
 variables=list(eq['variables']);rows=list(eq['residuals']);guardmap=[]
 for old in sorted(guards):
  idx=mapping[old];aux=[]
  for j in range(3):aux.append(len(variables));variables.append({'name':'triangular.'+str(idx)+'.'+str(j),'kind':'integer_auxiliary'})
  terms=[[2,[idx]]]
  for j in aux:terms.extend([[-1,[j]],[-1,[j,j]]])
  rows.append({'label':'nonnegative.'+str(idx),'terms':terms});guardmap.append({'raw':old,'exported':idx,'auxiliaries':aux})
 P=collections.defaultdict(int)
 for row in rows:
  for a,ma in row['terms']:
   for b,mb in row['terms']:P[tuple(sorted(ma+mb))]+=a*b
 P={m:c for m,c in P.items() if c};metrics={'integer_variables':len(variables),'quadratic_residuals':len(rows),'degree':max(map(len,P)),'monomials':len(P),'coefficient_height':max(map(abs,P.values())),'nonnegativity_seeds':len(guards),'normalized_semantic_pivots':len(pivots),'unrestricted_integer_quotients':len(free)}
 args.output.mkdir(parents=True,exist_ok=True);out={'format':'explicit_quadratic_residuals_v1','domain':'integers','variables':variables,'residuals':rows,'metrics':metrics};poly={'format':'ordinary_sparse_polynomial_v1','domain':'integers','variable_count':len(variables),'terms':[[c,list(m)] for m,c in sorted(P.items())]}
 payload={'actions':actions,'guard_map':guardmap,'raw_seed_indices':sorted(guards),'normalized_pivots':sorted(pivots),'rules':cert['rules'],'application_order':proof,'required_semantic_variables':sorted(required),'known_nonnegative_variables':sorted(known),'unrestricted_integer_quotients':sorted(free)}
 hashes={name:integer.write(args.output/name,obj) for name,obj in [('equation.json',out),('expanded_polynomial.json',poly),('normalization_certificate.json',payload)]}
 receipt={'metrics':metrics,'sha256':hashes,'core_sha256':hashlib.sha256((args.source/'equation.json').read_bytes()).hexdigest(),'predecessor_sign_certificate_sha256':hashlib.sha256((args.prior_integer/'sign_certificate.json').read_bytes()).hexdigest(),'scope':'exact finite sign action/parity verification and inherited sign closure; existential equivalence, not pointwise positivity; not kernel certification'};integer.write(args.output/'BUILD.json',receipt);print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
