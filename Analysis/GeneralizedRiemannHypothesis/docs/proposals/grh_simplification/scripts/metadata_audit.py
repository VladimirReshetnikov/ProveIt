from pathlib import Path
import re,json,csv,argparse
parser=argparse.ArgumentParser(description="Audit selected legacy exact-modulus declarations.")
parser.add_argument("repository",type=Path)
parser.add_argument("--output",type=Path,required=True)
args=parser.parse_args()
root=args.repository.resolve()/'Analysis/GeneralizedRiemannHypothesis/Lean/grh/src/New/Determinant'
out=args.output.resolve()
out.mkdir(parents=True,exist_ok=True)
# Exact old-representation declarations. Arithmetic/tameness and mixed-Gram adapters excluded.
names={
'Chain/Moduli.lean': ['lRatioProd','lRatioProd_nonneg','CriticalPair.ofReal_lRatioProd','CriticalPair.lRatioProd_eq_prod_norm_div','CriticalPair.lRatioProd_one_pow','HasAbsUpToNormPower','HasAbsUpToNormPower.mul','HasAbsUpToNormPower.one','HasAbsUpToNormPower.const','HasAbsUpToNormPower.inv','HasAbsUpToNormPower.prod','HasAbsUpToNormPower.exists_norm_div_eq','IsRamifiedRatio','IsRamifiedRatio.nonneg','IsRamifiedRatio.apply_one','quotientRatio','quotientRatio_add_eq_lRatioProd','isRamifiedRatio_quotientRatio'],
'Chain/NormOfChain.lean':['isRamifiedRatio_of_mem_sigma','prod_quotientRatio_one','prod_quotientRatio_nonneg','HasAbsUpToNormPower.exists_norm_div_eq_mul_prod_quotientRatio','HasSmallRatios.heightLe_inv_rpow_mul_prod_quotientRatio'],
'AuxiliaryForms/Turns.lean':['turnRatio','isRamifiedRatio_turnRatio','isRamifiedRatio_turnRatio_of_mem'],
'Twist/LongForms.lean':['HasSmallRatios.heightLe_inv_rpow_mul_prod_turnRatio'],
}
def strip_comments(s):
 result=[];i=0;depth=0
 while i<len(s):
  if depth:
   if s.startswith('/-',i):result.extend('  ');depth+=1;i+=2
   elif s.startswith('-/',i):result.extend('  ');depth-=1;i+=2
   else:result.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s.startswith('/-',i):result.extend('  ');depth=1;i+=2
  elif s.startswith('--',i):
   e=s.find('\n',i)
   if e==-1:e=len(s)
   result.extend(' '*(e-i));i=e
  else:result.append(s[i]);i+=1
 return ''.join(result)
rows=[]
for rel,targets in names.items():
 source=(root/rel).read_text();lines=source.splitlines(); clean=strip_comments(source).splitlines()
 decls={}
 for i,l in enumerate(clean):
  m=re.match(r'(?:(?:noncomputable|private|protected) )*(?:def|lemma|theorem|structure|abbrev) ([^\s({:]+)',l)
  if m:decls[m[1]]=i
 for name in targets:
  i=decls[name];j=i+1
  while j<len(lines) and not (clean[j].strip() and not clean[j][0].isspace()):j+=1
  while j>i+1 and not clean[j-1].strip():j-=1
  # Include immediately preceding documentation only, without unrelated top-level commands.
  ds=i
  k=i-1
  while k>=0 and not clean[k].strip():k-=1
  prefix='\n'.join(lines[k+1:i])
  docstart=prefix.find('/--')
  if docstart>=0:
   ds=k+1+prefix[:docstart].count('\n')
  rows.append(dict(file=rel,name=name,start=i+1,end=j,body_lines=j-i,code_lines=sum(bool(x.strip()) for x in clean[i:j]),doc_start=ds+1,documented_lines=j-ds))
with (out/'metadata_only_audit.tsv').open('w') as f:
 writer=csv.DictWriter(f,fieldnames=list(rows[0]),delimiter='\t');writer.writeheader();writer.writerows(rows)
summary={}
for rel in names:
 rr=[r for r in rows if r['file']==rel]
 summary[rel]={k:sum(r[k] for r in rr) for k in ['body_lines','code_lines','documented_lines']};summary[rel]['declarations']=len(rr)
print(json.dumps(summary,indent=2))
print('TOTAL',len(rows), {k:sum(r[k] for r in rows) for k in ['body_lines','code_lines','documented_lines']})

