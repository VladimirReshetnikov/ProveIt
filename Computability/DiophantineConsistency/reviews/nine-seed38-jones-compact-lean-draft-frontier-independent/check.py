import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-compact-lean-draft';q=D/'research/nine-seed38-jones-compact-macro-prototype'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
pins={'Norm38MacroLanguage.lean':'18ecac5f271aafd336133d48d8fdf9357e06dda7ca649712a801e71097a0e624','Norm38MacroRecipe.lean':'3756c5e056e9bfedd28aa1fca5d5aa01c6bbde8163332c70abced196cf6d3979','quote.py':'21e781a1f13a315bcb065650fc19ea0143ea36408826b3ee086f885be5d13c2b'}
for k,h in pins.items():assert sha(p/k)==h,k
assert sha(q/'recipe.json')=='779cd1d65dd84a4d5db6dd2072e94a7807b35394f5c245917b3688cc8ab2c090';subprocess.run([sys.executable,'-I','-S','-B',str(p/'quote.py'),'--check'],check=True,stdout=subprocess.DEVNULL,timeout=30)
d=json.loads((q/'recipe.json').read_text());rows=d['nodes'];names=[x['name'] for x in rows];assert len(names)==45 and d['output']=='output'
# Decode the actual generated Lean constructors, independently of quote.py.
pat=re.compile(r'\s*(\.[A-Za-z][A-Za-z0-9]*|⟨|⟩|\(|\)|:|,|-?\d+|[A-Za-z][A-Za-z0-9]*)')
def decode(text,prior):
 ts=[];pos=0
 while pos<len(text):
  m=pat.match(text,pos);assert m,(text[pos:],pos);ts.append(m.group(1));pos=m.end()
 j=0
 def eat(x):
  nonlocal j
  assert ts[j]==x,(ts[j],x);j+=1
 def parse(isnat=False):
  nonlocal j
  eat('(');op=ts[j];j+=1
  if isnat:
   if op=='.lit':v=['lit',int(ts[j])];j+=1
   elif op=='.index':v=['index','r']
   elif op=='.expo':v=['expo','k']
   elif op in ('.add','.sub','.mul','.pow'):v=[op[1:],parse(True),parse(True)]
   else:raise ValueError(op)
  else:
   if op=='.constant':eat('(');v=['const',int(ts[j])];j+=1;eat(':');eat('Int');eat(')')
   elif op in ('.input','.ref'):
    eat('⟨');ix=int(ts[j]);j+=1;eat(',');eat('by');eat('decide');eat('⟩');assert op!='.ref' or ix<prior;v=['var',ix] if op=='.input' else ['ref',names[ix]]
   elif op in ('.fixedZ','.fixedY'):v=['fixed','z' if op=='.fixedZ' else 'y']
   elif op=='.pcoef':v=['pcoef','k']
   elif op in ('.add','.sub','.mul'):v=[op[1:],parse(),parse()]
   elif op=='.pow':v=['pow',parse(),parse(True)]
   elif op=='.sumRange':v=['sum_range','r',parse(True),parse()]
   elif op=='.sumStar':v=['sum_star','k',parse()]
   else:raise ValueError(op)
  eat(')');return v
 val=parse();assert j==len(ts),(j,len(ts));return val
lines=(p/'Norm38MacroRecipe.lean').read_text().splitlines();matches=[re.fullmatch(r'  let d(\d+) : Dag (\d+) := \.snoc d(\d+) (.*)',x) for x in lines if ' := .snoc ' in x];assert len(matches)==45
for j,m in enumerate(matches):
 assert m is not None and [int(m.group(i)) for i in (1,2,3)]==[j+1,j+1,j];assert decode(m.group(4),j)==rows[j]['expr'],rows[j]['name']
text=(p/'Norm38MacroRecipe.lean').read_text();assert 'def WellScopedTarget : Prop := recipe.scoped = true' in text and 'def SemanticTarget : Prop :=' in text and 'recipe.values a (Fin.last 44) = Norm38IPRAEndpoint.expression.evalRing a' in text and 'theorem SemanticTarget' not in text
lang=(p/'Norm38MacroLanguage.lean').read_text()
for a in ['| .sub a b => a.eval r k - b.eval r k','| .expo => codingExpo 38 4 k','| .fixedZ => (indexZ seed 0 : R)','| .fixedY => (indexY seed 0 : R)','| .pcoef => (pCoefficient seed k : R)','Fin.snoc prev (entry.eval a prev 0 (fun _ => 0))']:assert a in lang,a
print(json.dumps({'status':'PASS_SOURCE_ONLY_TRANSLATION_REVIEW','pins':pins,'independently_decoded_nodes':45,'scope':'Independent decoder checks generated Lean source against pinned JSON; draft language had failed reserved prefix and targets remain unproved; no verified parser or Lean semantic theorem.'},indent=2,sort_keys=True))
