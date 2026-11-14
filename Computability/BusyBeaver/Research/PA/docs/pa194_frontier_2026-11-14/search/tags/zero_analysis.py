import json,collections,pathlib,sys,tempfile
ROOT=pathlib.Path(__file__).resolve().parent
p=ROOT/'reference/inputs/primary.instructions.json'
code=json.loads(p.read_text()); seen=[set() for _ in code]; todo=collections.deque([(25,1)])
while todo:
 i,m=todo.popleft()
 if m in seen[i]:continue
 seen[i].add(m)
 ins=code[i];op=ins[0]
 if op=='inc':out=[(ins[2],m|1<<ins[1])]
 elif op=='dec':
  b=1<<ins[1]
  out=[(ins[2],m)] if not(m&b) else [(ins[3],m),(ins[3],m^b)]
 elif op=='jump':out=[(ins[1],m)]
 else:out=[]
 todo.extend(out)
print('sites',len(code),'reachable',sum(bool(s) for s in seen),'contexts',sum(map(len,seen)))
for a in range(9):
 for b in range(a+1,9):
  both=[i for i,s in enumerate(seen) if any((m>>a&1)and(m>>b&1)for m in s)]
  cross=[i for i,s in enumerate(seen) if code[i][0] in ('inc','dec') and code[i][1] in (a,b) and any(m>>(b if code[i][1]==a else a)&1 for m in s)]
  print('pair',a,b,'both',len(both),'cross',len(cross))
knownzero=[]
for i,(ins,s) in enumerate(zip(code,seen)):
 if s and ins[0]=='dec' and all(not(m>>ins[1]&1)for m in s):knownzero.append(i)
print('always-zero decs',knownzero)
(pathlib.Path(sys.argv[1]) if len(sys.argv)>1 else pathlib.Path(tempfile.mkdtemp(prefix='pa-zero-'))/'zero_analysis.json').write_text(json.dumps({'input':str(p),'contexts':sum(map(len,seen)),'knownzero':knownzero,'masks':[sorted(s)for s in seen]}))
