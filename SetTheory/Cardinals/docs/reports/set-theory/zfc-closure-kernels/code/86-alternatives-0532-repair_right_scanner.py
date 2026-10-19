import pathlib,os,sys,importlib.util,json,time,collections
OUT=pathlib.Path(__file__).resolve().parent
R=OUT.parent/'context_folds'
os.environ['ZFC246_BASE']=str(R/'recovered/63');os.environ['ZFC246_TABLE']=str(R/'recovered/63/machine/zfc_prefix246_old.tm')
p=R/'recovered/64/experiments/decoder/fold_search246.py';sp=importlib.util.spec_from_file_location('f',p);f=importlib.util.module_from_spec(sp);sys.modules['f']=f;sp.loader.exec_module(f)
table={k:v for k,v in f.T.items()if k[0]!='74'};table['58',0]=(0,'R','84');states=sorted({q for q,b in table},key=int)
# Every one-row repair not visited before the baseline cutoff is unchanged on
# that entire rejecting prefix. This only excludes that finite proof family.
probe=f.Tracking(table);assert not f.check(probe,57,5000)[0]
rows=sorted(probe.used-f.P,key=lambda k:(int(k[0]),k[1]));rows=[k for k in rows if k in table]
order=[57,957]+[i for i in range(8391)if i not in(57,957)]
counts=collections.Counter();survivors=[];began=time.monotonic();journal=[]
print('rows',len(rows),rows,'first cases',[(i,f.CASES[i][:4])for i in order[:2]],flush=True)
for row in rows:
 for w in(0,1):
  for d in('L','R'):
   for q in states:
    counts['recipes']+=1;t=dict(table);t[row]=(w,d,q)
    for at,i in enumerate(order):
     counts['checks']+=1;ok,steps,why=f.check(t,i,5000)
     if not ok:
      counts['reject_'+why]+=1
      if at>1:order.insert(1,order.pop(at))
      journal.append([list(row),[w,d,q],i,why]);break
    else:
     hit={'row':list(row),'action':[w,d,q],'cases':8391};survivors.append(hit);print('SURVIVOR',hit,flush=True)
     (OUT/f'right_repair245_{len(survivors)}.tm').write_text('#! start 95\n'+''.join(f'{a} {b} {ww} {dd} {ss}\n'for(a,b),(ww,dd,ss)in sorted(t.items(),key=lambda z:(int(z[0][0]),z[0][1]))))
 print('row done',row,'elapsed',round(time.monotonic()-began,2),'counts',dict(counts),flush=True)
 out={'status':'complete'if row==rows[-1]else'running','fixed_shortening':['delete74','58/0=0R84'],'fuel':5000,'rows':rows,'counts':dict(counts),'seconds':time.monotonic()-began,'survivors':survivors}
 (OUT/'right_scanner_repairs.json').write_text(json.dumps(out,indent=2)+'\n')
(OUT/'right_scanner_repairs_journal.json').write_text(json.dumps(journal,separators=(',',':'))+'\n')
