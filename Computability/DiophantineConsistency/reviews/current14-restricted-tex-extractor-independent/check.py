from pathlib import Path
from hashlib import sha256
import json,ast,re,sys,importlib.util
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/current14-restricted-tex-extractor-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
tex=Path('equation.tex').read_text()
quote=Path('research/current14-seed-readable-prefix-staged-check/src/DiophantineConsistency/Current14QuotedPrefixQuote.lean').read_text()
core=Path('research/current14-seed-readable-prefix-staged-check/src/DiophantineConsistency/Current14QuotedPrefixCore.lean').read_text()
quoted=ast.literal_eval(re.search(r'def quoted : List \(List String\) := (\[.*?\]\])\s*\n\ndef quotedExpr',quote,re.S).group(1))
variables=['J','F','alpha','z','f','i','T','s','w','n','eta','zeta','y','gamma']
ports=['beta','K','mu','omega']
assert re.findall(r'\("([A-Za-z]+)", \.var (\d+)\)',core)==[(x,str(i)) for i,x in enumerate(variables)]
assert re.findall(r'\("(beta|K|mu|omega)", \.constant \(p (\d)\)\)',core)==[(x,str(i)) for i,x in enumerate(ports)]
assert re.search(r'The only unknowns are\s*\\\[\s*J,F,\\alpha,z,f,i,T,s,w,n,\\eta,\\zeta,y,\\gamma\\in\\mathbb Z_\{>0\}\.\s*\\\]',tex)
marker='All other symbols in the equation are polynomial abbreviations:'
assert tex.count(marker)==1
fragment=tex.split(marker,1)[1].split('\\begin{gathered}',1)[1].split('\\end{gathered}',1)[0].strip()
assert fragment.endswith('.')
fragment=fragment[:-1].replace('\\quad','').replace('\\\\','')
raw=fragment.split(',');assert len(raw)==22
final=re.search(r'The single equation is\s*\\\[\s*\\boxed\{([^{}]+)\}\s*\\\]',tex).group(1)
assert final.endswith('=0.')
# Independent shunting-yard parser for the actual restricted input.
def tokenize(s):
 matches=list(re.finditer(r'\s+|\\[A-Za-z]+|[A-Za-z1-4]|[-+^()\[\]]',s))
 assert ''.join(m.group() for m in matches)==s
 return [m.group()[1:] if m.group().startswith('\\') else m.group() for m in matches if not m.group().isspace()]
def parse(s,known):
 tok=tokenize(s);expanded=[]
 def end(x):return x in known or x in (')',']')
 def start(x):return x in known or x in ('(','[')
 for i,x in enumerate(tok):
  if i and end(tok[i-1]) and start(x):expanded.append('*')
  expanded.append(x)
 prec={'+':1,'-':1,'*':2,'^':3};ops=[];stack=[]
 def apply():
  op=ops.pop();b=stack.pop();a=stack.pop()
  if op=='^':
   assert b in ('2','3');stack.append(('sq' if b=='2' else 'cube',a))
  else:stack.append((op,a,b))
 for x in expanded:
  if x in known:stack.append(x)
  elif x in ('(','['):ops.append(x)
  elif x in (')',']'):
   target='(' if x==')' else '['
   while ops and ops[-1]!=target:apply()
   assert ops and ops.pop()==target
  else:
   assert x in prec,(x,s,known)
   while ops and ops[-1] in prec and (prec[ops[-1]]>prec[x] or (prec[ops[-1]]==prec[x] and x!='^')):apply()
   ops.append(x)
 while ops:apply()
 assert len(stack)==1
 def prefix(v):return [v] if isinstance(v,str) else [v[0]]+sum((prefix(a) for a in v[1:]),[])
 return prefix(stack[0])
known=set(variables+ports+['1','2','3','4']);independent=[]
for part in raw:
 lhs,rhs=part.split('=');name=''.join(lhs.split());name=name[1:] if name.startswith('\\') else name
 assert name not in known
 independent.append([name,'=']+parse(rhs,known));known.add(name)
independent.append(['result','=']+parse(final[:-3],known))
assert independent==quoted and len(independent)==23
# Check pinned parser's tested and untested boundaries on explicit mutations.
spec=importlib.util.spec_from_file_location('audited',Path('research/current14-restricted-tex-prefix-extractor/extract.py'));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
assert m.extract(tex)==independent
for old,new in [('b=\\beta J','b=q'),('q=b+1','q=b+M'),('Y=sq^3','Y=sq^4')]:
 assert old in tex
 try:m.extract(tex.replace(old,new,1))
 except m.ParseError:pass
 else:raise AssertionError('invalid source accepted '+old)
# The pinned checker searches the ordered substring only; these source mutations
# leave it and arithmetic extraction unchanged, despite changing TeX context.
phrase=tex.replace('The only unknowns are','Some named expressions are',1)
assert phrase!=tex and m.extract(phrase)==independent
ordered=r'J,F,\alpha,z,f,i,T,s,w,n,\eta,\zeta,y,\gamma\in\mathbb Z_{>0}'
assert ordered in phrase
redefined=tex.replace('\\begin{document}','\\renewcommand{\\Delta}{X}\n\\begin{document}',1)
assert redefined!=tex and m.extract(redefined)==independent and ordered in redefined
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'independent_shunting_yard_lines':len(independent),'matches_lean_quote':True,
 'actual_phrase_and_ordered_mapping_checked':True,'forward_unknown_exponent_mutations_rejected':True,
 'checker_does_not_check_declaration_phrase':True,'macro_redefinition_not_detected':True,
 'python_source_evidence_only':True,'lean_executed':False},indent=2,sort_keys=True))
