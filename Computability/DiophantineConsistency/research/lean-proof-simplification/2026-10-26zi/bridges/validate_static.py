from pathlib import Path
import re,json,hashlib
ROOT=Path(__file__).resolve().parent
SRC=ROOT.parent/'sources/Computability/DiophantineConsistency/Lean/DiophantineConsistency'

def mask_comments(text):
 out=[]; i=0; depth=0
 while i<len(text):
  if depth:
   if text[i:i+2]=='/-': depth+=1;out.extend('  ');i+=2
   elif text[i:i+2]=='-/':depth-=1;out.extend('  ');i+=2
   else:out.append('\n' if text[i]=='\n' else ' ');i+=1
  elif text[i:i+2]=='/-':depth=1;out.extend('  ');i+=2
  elif text[i:i+2]=='--':
   while i<len(text) and text[i]!='\n':out.append(' ');i+=1
  else:out.append(text[i]);i+=1
 assert depth==0
 return ''.join(out)

def decls(text):
 t=mask_comments(text)
 starts=list(re.finditer(r'^(private )?(theorem|lemma|def|structure|inductive)\s+([^\s:(]+)',t,re.M))
 ans={}
 for i,m in enumerate(starts):
  end=starts[i+1].start() if i+1<len(starts) else t.find('\nend ',m.start())
  if end<0:end=len(t)
  block=t[m.start():end]
  sig=block.split(':=',1)[0] if m[2] in ('theorem','lemma') else block
  ans[m[3]]={'kind':m[2],'private':bool(m[1]),'signature_or_definition':' '.join(sig.split())}
 return ans

reports=[]
for name in ('WangTiles942TraceCycle.lean','WangTiles942FinishConstruction.lean'):
 a=(SRC/name).read_text();b=(ROOT/'candidate'/name).read_text();da,db=decls(a),decls(b)
 for n,v in da.items():assert db[n]==v,(name,n)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',mask_comments(b))
 reports.append({'file':name,'preserved_existing_declarations':len(da),'new_declarations':sorted(set(db)-set(da)),'existing_signatures_and_entire_definitions_equal_mod_comments_whitespace':True})

I=('initializer-input',);F=('finish-reset-interface',)
def S(n):return ('actual-run-color',n)
def ports(H,k):
 if k==0:return I,S(1)
 if k+1==H:return F,I
 if k+2==H:return S(k),F
 return S(k),S(k+1)
def seam(H,k):
 if k+1==H:return I
 if k+2==H:return F
 return S(k+1)
checks=0
for H in range(3,33):
 for k in range(H):
  assert ports(H,(k+1)%H)[0]==ports(H,k)[1]==seam(H,k)
  checks+=1
negative={H:ports(H,1%H)[0]!=ports(H,0)[1] for H in (1,2)}
assert all(negative.values())
colors=sorted({432*a+b for a in (0,1) for b in (0,1)})
assert colors==[0,1,432,433] and 4 not in colors
report={'validation':'STATIC/MODEL ONLY, NOT Lean elaboration or proof checking','declaration_checks':reports,'symbolic_cycle_seams':{'height_min':3,'height_max':32,'cases':checks,'small_height_negative_controls':negative,'comment':'Treats every distinct actual-run color/time as an opaque symbol; checks branch chronology only.'},'closing_constructor_color_model':{'colors':colors,'operating_initialized_head_4_excluded':True,'comment':'Checks the shared Fin2 formula only, not a separate enumeration of the Allowed language.'},'lean_invocations':0,'runtime_installations':0}
(ROOT/'validation/static_and_model.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
