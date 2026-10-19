import pathlib,importlib.util,sys,os,inspect,itertools,json,collections
R=pathlib.Path(__file__).resolve().parent
os.environ['ZFC246_BASE']=str(R/'recovered/63');os.environ['ZFC246_TABLE']=str(R/'recovered/63/machine/zfc_prefix246_old.tm')
p=R/'recovered/64/experiments/decoder/fold_search246.py';spec=importlib.util.spec_from_file_location('f',p);f=importlib.util.module_from_spec(spec);sys.modules['f']=f;spec.loader.exec_module(f)
patterns=collections.Counter();examples={}
def bits(segs,n):
 result=[]
 for s in segs:
  if s[0]=='b':result.append(s[1])
  elif s[0]=='r':
   _,b,c,a=s;result.extend([b]*min(n-len(result),a))
   if c and len(result)<n:return result+[None]*(n-len(result))
  elif s[0]=='box':
   kind,data=s[1];result.extend([0,0 if kind=='mark' and data==0 else 1]);return (result+[None]*n)[:n]
  else:raise Exception(s)
  if len(result)>=n:return result[:n]
 return result+[0]*(n-len(result))
current=None
def hook(onleft,left,right):
 assert onleft
 lb=bits(left,10);rb=bits(right,24)
 assert rb[:2]==[0,1], (current,"right",right,rb)
 k=next((i for i,b in enumerate(lb[:9])if b==1),8)
 assert all(b==0 for b in lb[:k]), (current,"left",left,lb,k)
 if k==6:assert rb[2:12]==[1]*10,(current,k,rb)
 if k==7:assert rb[2:13]==[1]*11,(current,k,rb)
 if k==8:
  assert lb[:9]==[0]*9,(current,k,lb)
  assert 0 in rb[2:13],(current,k,rb)
 pat=(k,tuple(rb[2:13])if k>=6 else(),lb[k+1]if k<8 else None)
 patterns[pat]+=1;examples.setdefault(pat,current)
src=inspect.getsource(f.A.run);needle='    for _ in range(fuel):\n';src=src.replace(needle, '    seen6=False\n'+needle+'        if q=="6" and not seen6: detector_hook(onleft,left,right)\n        seen6=(q=="6")\n');f.A.detector_hook=hook;exec(src,f.A.__dict__)
for i,c in enumerate(f.CASES):
 current=i; p,op,r,z,g,w=c; f.A.run(f.T,p,g,w,halt=op=='CH',fuel=1000)
out=[]
for(k,r,l),ct in sorted(patterns.items(),key=str):out.append({'k':k,'right_3_22':r,'left_after_one':l,'count':ct,'example_case':examples[k,r,l]})
(R/'deeper_entry_guard.json').write_text(json.dumps({'status':'PASS','cases':8391,'entries':sum(patterns.values()),'guard':'At state6: k6 implies +3..+12 all1; k7 implies +3..+13 all1; long implies at least one0 in+3..+13. Existing short0..7/long-zero partition retained.','symbolic_patterns':out},indent=2)+'\n')
for k in range(9):
 p={r[:2]for(kk,r,l)in patterns if kk==k};print(k,'right3_4 patterns',p,'total patterns',sum(kk==k for kk,r,l in patterns))
