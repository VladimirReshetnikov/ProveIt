from pathlib import Path
import sys,json
p=Path('/workspace/scratch/f42aca38d186/ProveIt/Computability/BusyBeaver/Research/ZFC/candidate-k215')
sys.path[:0]=[str(p),str(p/'code')]
import source_language as s,build221 as b
rows=json.loads((p/'sites215.json').read_text());old=s.tree(rows);T=b.read_table((p/'k215.native.tm').read_bytes());groups,ps=b.decoder_map(T,old)
flat=lambda x:[tuple(r[1:])for r in s.sites(x)]
macros={'a':b.sole(groups,98),'b':b.sole(groups,12),'c':b.sole(groups,166),'I':b.sole(groups,90)}
inc=('CI',1);macros.update(R=(macros['I'],inc),Q=(macros['I'],(inc,inc)),E=(macros['I'],((inc,inc),inc)),F=(macros['a'][0],inc))
words={k:flat(v)for k,v in macros.items()};tokens=[];rr=[tuple(r[1:])for r in rows];i=214
while i<4556:
 choices=[k for k,w in words.items()if rr[i:i+len(w)]==w]
 if not choices:raise ValueError((i,rr[i:i+8]))
 k=max(choices,key=lambda k:len(words[k]));tokens.append((i,i+len(words[k]),k));i+=len(words[k])
assert i==4556
omits=[]
for pth in ps[164]:
 p0=pth+'1';inds=[i for i,r in enumerate(rows)if r[0].startswith(p0)];lo,hi=min(inds),max(inds)+1
 print('omit',pth,lo,hi,next((j for j,(a,z,k)in enumerate(tokens)if a==lo and z==hi),None));omits.append(lo)
print('tokens',''.join(k for a,z,k in tokens))
stack=['top'];label=0
for j,(lo,hi,k)in enumerate(tokens):
 if k in'abcF':
  v=1 if k=='F'else k
  if lo in omits:stack[-1]=('+',stack[-1],v);k+='*'
  else:stack.append(v)
 else:
  right=stack.pop();left=stack.pop();stack.append((k,left,right))
 print(j,lo,hi,k,'stackdepth',len(stack),'current',repr(stack[-1]))
print('FINAL',stack)
