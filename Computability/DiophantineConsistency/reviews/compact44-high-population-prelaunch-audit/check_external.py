#!/usr/bin/env python3
"""Independently parse high list and reconstruct finite retained high integer."""
import gzip,hashlib,importlib.util,json,re,sys
from pathlib import Path
BASE=Path(__file__).resolve().parents[2];PKG=BASE/'research/ordinary12-ipra-bridge/compact44-high-population-prototype';RECIPE=BASE/'candidates/free-j-polarized-positive/source/positive/coefficients/recipe';COEF=BASE/'candidates/ten-positive-shifted-strong/coefficients'
PINS={PKG/'CompactHighPopulation.lean':'b1e962aed2f9fc2b49533a52f3508a84af4d433c4a9fae210540e085056dab1d',RECIPE/'build_coefficients.py':'a003f26c5ef2dc1782e37be2a91abe25e59e5ff39f12bd142f2d6c1d4d8cf82b',RECIPE/'k215_transitions.json':'880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755',COEF/'MF_source.bin.gz':'935cd87f8b23f24a20fd742c48d2a9cbca6afd494b6b074445df72c98b0c6e3b',COEF/'beta.bin.gz':'466796f146d60db9929fa0f0f62d70d5e6afbcea9940342764571f1ca6bea87c'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
def main():
 for p,h in PINS.items():need(sha(p)==h,'pin '+str(p))
 source=(PKG/'CompactHighPopulation.lean').read_text(); match=re.search(r'def highDigits : List ℕ :=\s*(.*?)\n\ntheorem digits_length',source,re.S);need(match and source.count('def highDigits :')==1,'list definition')
 const={'mu':2**51-2,'padding':2**65-1,'lastPadding':2**19-1};need(all(source.count(f'def {k} : ℕ := 2^{p}-{q}')==1 for k,p,q in [('mu',51,2),('padding',65,1),('lastPadding',19,1)]),'constants')
 digits=[]
 for term in match[1].split('++'):
  term=term.strip();rep=re.fullmatch(r'List\.replicate\s+(\d+)\s+(\w+)',term)
  if rep:
   value=const.get(rep[2],None);value=int(rep[2]) if rep[2].isdigit() else value;need(value is not None,'unknown replicate digit');digits.extend([value]*int(rep[1]));continue
  lit=re.fullmatch(r'\[([^]]*)\]',term);need(lit is not None,'unexpected list syntax')
  for token in lit[1].split(','):
   token=token.strip();value=int(token) if token.isdigit() else const.get(token);need(value is not None,'unknown digit');digits.append(value)
 need(len(digits)==8807 and all(0<=x<2**67 for x in digits),'bounds/length')
 pop=sum(x.bit_count() for x in digits);need(pop==986,'population')
 high=sum(x << (67*i) for i,x in enumerate(digits) if x)
 beta=int.from_bytes(gzip.decompress((COEF/'beta.bin.gz').read_bytes()),'little');shift=int.from_bytes(gzip.decompress((COEF/'MF_source.bin.gz').read_bytes()),'little')
 need(beta==2**590069-1 and shift>=beta and shift-beta==high,'retained difference')
 need(all((high>>(67*i))%(2**67)==x for i,x in enumerate(digits)),'all digits')
 sys.dont_write_bytecode=True;sp=importlib.util.spec_from_file_location('review_recipe',RECIPE/'build_coefficients.py');module=importlib.util.module_from_spec(sp);sp.loader.exec_module(module);r=module.recipe()
 expected={0:4,4393:r['mu'],5495:r['mu']}
 for t,*_ in r['targets']:expected[t]=expected.get(t,0)+1
 for e,v in r['padding'].items():expected[e]=expected.get(e,0)+v
 need(all(digits[i]==expected.get(i,0) for i in range(8807)),'independent builder positions')
 controls=[]
 for i in (0,2195,4393,8805):
  altered=digits.copy();altered[i]^=1;need(sum(x<<(67*j) for j,x in enumerate(altered) if x)!=high,'mutation '+str(i));controls.append(i)
 for p,h in PINS.items():need(sha(p)==h,'post pin '+str(p))
 print(json.dumps({'status':'PASS_INDEPENDENT_HIGH_LIST_EXTERNAL','length':len(digits),'digits_checked':len(digits),'population':pop,'nonzero_positions':len(expected),'mutations_rejected':controls,'scope':'Finite external source/recipe/bytes only; no Lean retained-port identity, mod-8 theorem, graph or iPRA proof.'},indent=2))
if __name__=='__main__':main()
