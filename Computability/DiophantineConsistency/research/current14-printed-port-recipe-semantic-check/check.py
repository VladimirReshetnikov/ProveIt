#!/usr/bin/env python3
"""Pinned TeX recipes, independently evaluated vs source-defined port data."""
from pathlib import Path
from hashlib import sha256
import gzip,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/current14-printed-port-recipe-semantic-check')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
tex=Path('equation.tex').read_text();a=tex.index(r'\textbf{The four fixed integers.}');b=tex.index(r'\textbf{The integer $\mathcal A$ in base 10.}',a)
assert tex[a:b]==(D/'printed-recipes.texfrag').read_text()
block=tex[b:].split('\\begingroup',1)[1].split('\\endgroup',1)[0]
lines=re.findall(r'\n(\d+)\\par',block)
assert len(lines)==12 and len(''.join(lines))==715
assert re.sub(r'^\\fontsize\{7\.7\}\{8\.2\}\\selectfont\\ttfamily\s*|\d+\\par|\s+','',block)==''
seed=int(''.join(lines));N=seed%(1<<636);payload=seed>>636
nu=[(N>>j)&1 for j in range(430)];sigma=[0]
for bit in nu:sigma.append(sigma[-1]+bit)
radices=[(sigma[j]+2)**(1-nu[j]) for j in range(430)];prefix=[1]
for x in radices:prefix.append(prefix[-1]*x)
mask=[(N>>(430+q))&1 for q in range(215)];tau=0;actions=[]
for q in range(215):
 m=mask[q];F=14+m*((payload//prefix[-1]//(16**tau))%16-14);tau+=m
 for b in range(2):
  j=2*q+b;u=(sigma[j+1]-(payload//prefix[j])%radices[j])%216
  actions.append((u,(F>>(2*b))&1,(F>>(2*b+1))&1))
assert actions[0]==(1,1,1)
S=[{u for u,v,d in actions if d==bit} for bit in (0,1)]
def rank(d,q):return 205-199*d+sum(x<q for x in S[d])
tiles={}
def put(i,t):
 assert i not in tiles and 0<=i<942 and all(x>=0 for x in t)
 tiles[i]=t
put(0,(2,435,3,1))
for j,(u,v,d) in enumerate(actions):put(j+1,((1-d)*rank(0,u),2*(j//2)+j%2+2,d*rank(1,u),v))
for aa in range(2):
 for bb in range(2):put(433-2*aa+bb,(0,432*aa+bb,0,432*aa+bb))
for d in (0,1):
 for q in sorted(S[d]):
  r=rank(d,q)
  for bb in range(2):put(423+2*r+bb,(d*r,bb,(1-d)*r,2*q+bb+2))
for aa in range(2):
 for bb in range(2):put(923+2*aa+bb,(0,432*aa+bb,0,438))
for i,t in ((927,(2,434,2,0)),(928,(3,436,4,4)),(929,(4,436,4,0))):put(i,t)
for t in (434,435,436):put(496+t,(1,438,1,t))
for aa in range(3):
 for bb in range(3):put(933+3*aa+bb,(aa*aa,437,bb,437))
assert set(tiles)==set(range(942))
def weight(t):w,n,p,s=t;return 1+2**10*(1+w+2**8*n+2**17*p+2**25*s)
weights=[weight(tiles[i]) for i in range(942)];assert all(0<x<2**44 for x in weights)
# Evaluate the printed floor formula, including its exceptional start at 0.
pos=[0]+[1+sum(((2**44-1+weights[j]-weights[i])//2**44) for j in range(1,942)) for i in range(1,942)]
assert set(pos)==set(range(942))
# Compare with the historical kernel's source-declared physical rows and order.
physical=Path('Lean/DiophantineConsistency/MFWangTiles942PhysicalData.lean').read_text()
parts=re.findall(r'def chunk(\d+) : List \(ℕ × ℕ\) := \[(.*?)\]',physical,re.S)
assert [n for n,_ in parts]==[f'{j:02d}' for j in range(59)]
expr=physical.split('def rows : List (ℕ × ℕ) :=',1)[1].split('theorem rows_length',1)[0]
assert re.findall(r'chunk\d+',expr)==[f'chunk{j:02d}' for j in range(59)]
rows=[]
for _,content in parts:
 assert not re.sub(r'\(\d+,\s*\d+\)|[\s,]','',content)
 rows += [(int(i),int(v)) for i,v in re.findall(r'\((\d+),\s*(\d+)\)',content)]
assert len(rows)==941 and rows==sorted([(i,weights[i]) for i in range(1,942)],key=lambda x:pos[x[0]])
table=Path('Lean/DiophantineConsistency/WangTiles942TableData.lean').read_text();start=re.search(r'def start : Tile := ⟨(\d+),\s*(\d+),\s*(\d+),\s*(\d+)⟩',table)
assert start and tuple(map(int,start.groups()))==tiles[0]
assert '1 + 2 ^ 10 * (1 + t.west + 2 ^ 8 * t.north + 2 ^ 17 * t.east + 2 ^ 25 * t.south)' in table
# Evaluate the displayed port recipes as integers after exact rational cancellation.
rho=2**47;B=rho**2011;beta=B-1;G=lambda n:sum(rho**j for j in range(n))
mu=beta-G(951)-rho**960*G(26)-rho**1004
omega=beta+8*G(917)-4+(2**45-4)*rho**1005+rho**960*G(9)+rho**987*G(8)+rho**1004
K=rho**18+rho**1004+rho**2020+sum(2*weights[i]*rho**(1005-pos[i]) for i in range(942))
for count,basepow,offset in ((8,10,978),(8,27,969),(9,18,960),(9,35,942)):
 K+=sum(2*2**(basepow+j)*rho**(1005-offset-j) for j in range(count))
# Independently evaluate the historical mask data, rather than assume equality.
mask=Path('Lean/DiophantineConsistency/CurrentMaskData2011.lean').read_text()
for tok in ('def radix : ℕ := 2 ^ 47','def beta : ℕ := radix ^ 2011 - 1','Finset.range 951 ∪ Finset.Ico 960 986 ∪ {1004}','def lowPort : ℕ := mask radix 2 2011 lowSupport','4 :: (List.replicate 916 8 ++ List.replicate 43 0 ++ List.replicate 9 1 ++','List.replicate 18 0 ++ List.replicate 8 1 ++ List.replicate 9 0 ++ [1, 2 ^ 45 - 4]','def highDigits : List ℕ := highPrefix ++ List.replicate 1005 0','def highPort : ℕ := Nat.ofDigits radix highDigits'):assert tok in mask
lowmask=Path('Lean/DiophantineConsistency/LowMaskData.lean').read_text()
assert 'B ^ len - 1 - (b-1) * supportValue B S' in lowmask
support=set(range(951))|set(range(960,986))|{1004};low=beta-sum(rho**i for i in support)
digits=[4]+[8]*916+[0]*43+[1]*9+[0]*18+[1]*8+[0]*9+[1,2**45-4]+[0]*1005
assert len(digits)==2011
high=sum(v*rho**i for i,v in enumerate(digits));assert mu==low and omega==beta+high
# Evaluate the independently stated source K recipe and compare exact integers.
recipe=Path('research/current2011-kernel-byte-recipe/KernelRecipe.lean').read_text()
section=recipe.split('def recipe (r : ℕ) : ℕ :=',1)[1].split('theorem rawWord_recipe',1)[0]
assert 'r ^ 18 + r ^ 1004 + r ^ 2020' in section and '(∑ p : Fin 942, 2 * weightAt p * r ^ (1005 - p.val))' in section
control=re.findall(r'∑ j : Fin (\d+), 2 \* 2 \^ \((\d+) \+ j.val\) \* r \^ \(1005 - \((\d+) \+ j.val\)\)',section)
assert control==[('8','10','978'),('9','18','960'),('8','27','969'),('9','35','942')]
reference=rho**18+rho**1004+rho**2020+sum(2*v*rho**(1005-i) for i,v in enumerate([weights[0]]+[v for _,v in rows]))
for count,power,offset in map(lambda x:tuple(map(int,x)),control):reference+=sum(2*2**(power+j)*rho**(1005-offset-j) for j in range(count))
assert K==reference and beta>0 and K>0 and mu>0 and omega>0
line=Path('research/nine-sharing-sign17-lines-current14-endpoint-check/src/DiophantineConsistency/Sign17LinesCurrent14Endpoint.lean').read_text()
for tok in ('(CurrentMasks2011.beta : ℤ), (Sign17LinesKernel.lineK : ℤ)','(CurrentMasks2011.lowPort : ℤ), ((CurrentMasks2011.highPort + CurrentMasks2011.beta : ℕ) : ℤ)','theorem linePorts_recipes'):assert tok in line
kernel=Path('research/nine-sharing-sign17-lines-kernel-check/src/DiophantineConsistency/Sign17LinesKernel.lean').read_text()
for tok in ('theorem linePosition_eq','theorem lineCoefficient_eq','theorem lineK_eq','lineK = K'):assert tok in kernel
# External graph payloads: compare bytes to independently evaluated ports.
graph=Path("candidates/one-page-padding-staircase-carrier65-2011/polynomial.json")
binding=json.loads(graph.read_text())["coefficient_binding"]
for key,value in (("beta",beta),("K0",K),("MC",mu),("MF",omega)):
 meta=binding["ports"][key];payload=graph.parent/binding["path"]/meta["file"]
 zipped=payload.read_bytes();raw=gzip.decompress(zipped)
 assert sha256(zipped).hexdigest()==meta["gzip_sha256"] and sha256(raw).hexdigest()==meta["raw_sha256"]
 assert len(raw)==meta["raw_bytes"] and int.from_bytes(raw,"big")==value and value.bit_length()==meta["bits"]
physical_order=Path("Lean/DiophantineConsistency/MFWangTiles942PhysicalOrder.lean").read_text()
assert "def weightAt (p : Fin 942) : ℕ := Fin.cases (selectorWeight start) value p" in physical_order
line_table=Path("research/nine-sharing-sign17-lines-table-check/src/DiophantineConsistency/Sign17LinesTable.lean").read_text()
assert "theorem lineTile_eq" in line_table and "theorem lineOrderedRows_eq" in line_table
# No printed giant numerals; use unambiguous positive big-endian hash values.
def digest(x):return sha256(x.to_bytes((x.bit_length()+7)//8,'big')).hexdigest()
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),'seed_decimal_digits':len(''.join(lines)),'decoded_actions':len(actions),'ordered_tiles':len(tiles),'physical_rows_match':len(rows),'exact_port_values_equal_to_source_recipes':True,'positive_ports':True,'display_graph_payload_bytes_match':True,'port_bits':{k:v.bit_length() for k,v in [('beta',beta),('K',K),('mu',mu),('omega',omega)]},'port_big_endian_sha256':{k:digest(v) for k,v in [('beta',beta),('K',K),('mu',mu),('omega',omega)]},'scope':'manual restricted TeX recipe interpretation compared to pinned source recipes; no formal TeX semantics or Lean run','lean_executed':False},sort_keys=True,indent=2))
