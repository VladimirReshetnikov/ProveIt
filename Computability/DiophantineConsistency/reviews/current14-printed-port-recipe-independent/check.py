from pathlib import Path
from hashlib import sha256
import json,re,gzip,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/current14-printed-port-recipe-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
T=Path('equation.tex').read_text(); start=T.index(r'\textbf{The four fixed integers.}');end=T.index(r'\textbf{The integer $\mathcal A$ in base 10.}',start)
assert T[start:end]==Path('research/current14-printed-port-recipe-semantic-check/printed-recipes.texfrag').read_text()
block=T[end:].split(r'\begingroup',1)[1].split(r'\endgroup',1)[0]
lines=re.findall(r'\n(\d+)\\par',block);assert len(lines)==12 and len(''.join(lines))==715
assert not re.sub(r'^\\fontsize\{7\.7\}\{8\.2\}\\selectfont\\ttfamily\s*|\d+\\par|\s+','',block)
seed=int(''.join(lines)); N=seed%(2**636); Tcode=seed//(2**636)
# Sequential Euclidean division gives the mixed-radix digits independently
# of the reviewed checker's growing-prefix-quotient implementation.
bits=[(N//2**j)%2 for j in range(430)]; c=0; digits=[];cum=[0]
for bit in bits:
 radix=(c+2)**(1-bit);Tcode,digit=divmod(Tcode,radix);digits.append(digit);c+=bit;cum.append(c)
flags=[]
for q in range(215):
 m=(N//2**(430+q))%2
 if m:Tcode,digit=divmod(Tcode,16);flags.append(digit)
 else:flags.append(14)
actions=[]
for j in range(430):
 F=flags[j//2];b=j%2
 actions.append(((cum[j+1]-digits[j])%216,(F//2**(2*b))%2,(F//2**(2*b+1))%2))
assert actions[0]==(1,1,1)
sets=[sorted(set(u for u,v,d in actions if d==i)) for i in range(2)]
def rank(d,q):return 205-199*d+len([x for x in sets[d] if x<q])
tiles={}
def add(i,v):
 assert i not in tiles and 0<=i<942 and len(v)==4 and min(v)>=0
 tiles[i]=v
add(0,(2,435,3,1))
for j,(u,v,d) in enumerate(actions):add(j+1,((1-d)*rank(0,u),j+2,d*rank(1,u),v))
for a in range(2):
 for b in range(2):add(433-2*a+b,(0,432*a+b,0,432*a+b))
for d in range(2):
 for q in sets[d]:
  r=rank(d,q)
  for b in range(2):add(423+2*r+b,(d*r,b,(1-d)*r,2*q+b+2))
for a in range(2):
 for b in range(2):add(923+2*a+b,(0,432*a+b,0,438))
for i,v in [(927,(2,434,2,0)),(928,(3,436,4,4)),(929,(4,436,4,0))]:add(i,v)
for t in [434,435,436]:add(496+t,(1,438,1,t))
for a in range(3):
 for b in range(3):add(933+3*a+b,(a*a,437,b,437))
assert set(tiles)==set(range(942))
weights=[]
for i in range(942):
 w,n,p,s=tiles[i];weights.append(1+2**10*(1+w+2**8*n+2**17*p+2**25*s))
assert all(0<x<2**44 for x in weights) and len(set(weights[1:]))==941
# The printed floor contributes 1 precisely when chi_j > chi_i.
order=[0]+sorted(range(1,942),key=lambda i:-weights[i]);pos={x:i for i,x in enumerate(order)}
for i in range(1,942):
 assert pos[i]==1+sum((2**44-1+weights[j]-weights[i])//2**44 for j in range(1,942))
physical=Path('Lean/DiophantineConsistency/MFWangTiles942PhysicalData.lean').read_text()
chunks=re.findall(r'def chunk(\d+) : List \(ℕ × ℕ\) := \[(.*?)\]',physical,re.S)
assert [n for n,_ in chunks]==[f'{j:02d}' for j in range(59)]
rowdef=physical.split('def rows : List (ℕ × ℕ) :=',1)[1].split('theorem rows_length',1)[0]
assert re.findall(r'chunk\d+',rowdef)==[f'chunk{j:02d}' for j in range(59)]
rows=[]
for _,content in chunks:
 assert not re.sub(r'\(\d+,\s*\d+\)|[\s,]','',content)
 rows.extend((int(a),int(b)) for a,b in re.findall(r'\((\d+),\s*(\d+)\)',content))
assert rows==[(i,weights[i]) for i in order[1:]]
# Horner evaluation of printed geometric sums and Phi coefficients.
rho=2**47;B=rho**2011;beta=B-1
mask_source=Path('Lean/DiophantineConsistency/CurrentMaskData2011.lean').read_text()
for text in ('def radix : ℕ := 2 ^ 47','def beta : ℕ := radix ^ 2011 - 1',
 'Finset.range 951 ∪ Finset.Ico 960 986 ∪ {1004}',
 'def lowPort : ℕ := mask radix 2 2011 lowSupport',
 '4 :: (List.replicate 916 8 ++ List.replicate 43 0 ++ List.replicate 9 1 ++',
 'List.replicate 18 0 ++ List.replicate 8 1 ++ List.replicate 9 0 ++ [1, 2 ^ 45 - 4]',
 'def highDigits : List ℕ := highPrefix ++ List.replicate 1005 0',
 'def highPort : ℕ := Nat.ofDigits radix highDigits'):assert text in mask_source
assert 'B ^ len - 1 - (b-1) * supportValue B S' in Path('Lean/DiophantineConsistency/LowMaskData.lean').read_text()
low_support=set(range(951))|set(range(960,986))|{1004}
low_digits=[rho-1-(1 if j in low_support else 0) for j in range(2011)]
def horner(ds):
 v=0
 for d in reversed(ds):v=v*rho+d
 return v
mu=horner(low_digits)
high_digits=[0]*2011
for j in range(917):high_digits[j]=8
high_digits[0]-=4
for j in range(960,969):high_digits[j]+=1
for j in range(987,995):high_digits[j]+=1
high_digits[1004]+=1;high_digits[1005]+=2**45-4
omega=beta+horner(high_digits)
coeff=[0]*2021
for j in [18,1004,2020]:coeff[j]+=1
for i in range(942):coeff[1005-pos[i]]+=2*weights[i]
for count,offset,power in [(8,978,11),(8,969,28),(9,960,19),(9,942,36)]:
 for j in range(count):
  exponent=1005-offset-j;assert exponent>=0
  coeff[exponent]+=2**(power+j)
K=horner(coeff)
recipe=Path('research/current2011-kernel-byte-recipe/KernelRecipe.lean').read_text().split('def recipe (r : ℕ) : ℕ :=',1)[1].split('theorem rawWord_recipe',1)[0]
assert 'r ^ 18 + r ^ 1004 + r ^ 2020' in recipe
assert '(∑ p : Fin 942, 2 * weightAt p * r ^ (1005 - p.val))' in recipe
controls=re.findall(r'∑ j : Fin (\d+), 2 \* 2 \^ \((\d+) \+ j.val\) \* r \^ \(1005 - \((\d+) \+ j.val\)\)',recipe)
assert controls==[('8','10','978'),('9','18','960'),('8','27','969'),('9','35','942')]
graph=Path('candidates/one-page-padding-staircase-carrier65-2011/polynomial.json');binding=json.loads(graph.read_text())['coefficient_binding']
values={'beta':beta,'K0':K,'MC':mu,'MF':omega};hashes={}
for key,value in values.items():
 meta=binding['ports'][key];compressed=(graph.parent/binding['path']/meta['file']).read_bytes();raw=gzip.decompress(compressed)
 assert sha256(compressed).hexdigest()==meta['gzip_sha256'] and sha256(raw).hexdigest()==meta['raw_sha256']
 assert len(raw)==meta['raw_bytes'] and value.bit_length()==meta['bits'] and int.from_bytes(raw,'big')==value
 hashes[key]=sha256(raw).hexdigest()
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'seed_digits':len(''.join(lines)),
 'decoded_actions':len(actions),'all_indexed_tiles':len(tiles),'physical_order_rows':len(rows),
 'printed_rank_formulas_checked':941,'all_payloads_equal':True,'raw_payload_sha256':hashes,
 'manual_formula_interpretation':True,'lean_tex_pdf_semantics_proved':False,'lean_executed':False},indent=2,sort_keys=True))
