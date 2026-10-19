import independent_runtime as r
import json,time
ss=r.sites(json.loads((r.BASE/'candidate-routing245/grammar.json').read_text()))
t=r.table(r.BASE/'candidate-routing245/zfc_routing245_old.tm');assert t[75,0]==(1,1,255)
t[75,0]=(1,-1,131);t={k:v for k,v in t.items() if k[0]!=255}
count=0;bad=[];began=time.monotonic()
for profile,regs0,spares,gap in [('small',[0]*9,[1],0),('distinct',list(range(9)),[0,3,1],17),('mixed',[19,1,0,2,0,9,1,0,6],[0],0)]:
 for i,site in enumerate(ss):
  for pos in ((False,True) if site[1]=='CD' else (False,)):
   regs=regs0.copy()
   if site[1]=='CD':regs[site[2]]=max(1,regs[site[2]]) if pos else 0
   wanted=r.expected(site,regs,spares,gap)
   if site[1]=='CI':
    conf,log=wanted;log['spares'][-1]=0
    shift=-conf[1];wanted=((96,-shift,{v-shift for v in r.frame(log['pc'],log['registers'],log['spares'],log['gap_extra'])}),log)
   actual,steps,_=r.run(t,site[0],regs,spares,gap,limit=100000)
   ok=actual[0]==254 if wanted is None else actual==wanted[0]
   if not ok:
    entry={'profile':profile,'site_index':i,'site':site,'positive':pos,'steps':steps,'actual':r.describe(actual),'expected':r.describe(wanted[0]) if wanted else None,'registers':regs,'spares':spares,'gap_extra':gap};bad.append(entry)
    if len(bad)==1:
     _,_,tr=r.run(t,site[0],regs,spares,gap,trace=True);(r.OUT/'sparezero244_first_failure.json').write_text(json.dumps(dict(entry,trace=tr),indent=2)+'\n')
   count+=1
 print(profile,'cumulative cases',count,'failures',len(bad),flush=True)
report={'status':'FINITE_PASS' if not bad else 'FINITE_FAILURE','cases':count,'failures':len(bad),'seconds':time.monotonic()-began,'scope':'Three finite profiles, arbitrary-frame proof separate','first_failure':bad[0] if bad else None}
(r.OUT/'sparezero244_regression.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
