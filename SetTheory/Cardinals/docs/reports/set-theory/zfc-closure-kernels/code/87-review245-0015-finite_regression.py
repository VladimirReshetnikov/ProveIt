"""Independent finite numerical regression; imports only our self-authored module."""
import independent_runtime as r
import json,time
base=r.sites(json.loads((r.BASE/'candidate-routing245/grammar.json').read_text()))
changed=json.loads((r.OUT/'obvious244-sites.json').read_text())
tables=[('baseline245',r.table(r.BASE/'candidate-routing245/zfc_routing245_old.tm'),base),('obvious244',r.table(r.OUT/'candidates/candidate_reassociation244_old.tm'),changed),('scanner244',r.table(r.OUT/'candidates/candidate_scanner244_old.tm'),base)]
reports=[]
for name,t,ss in tables:
    count=0;bad=[];began=time.monotonic()
    for i,site in enumerate(ss):
        for pos in ((False,True) if site[1]=='CD' else (False,)):
            regs=[0]*9
            if pos:regs[site[2]]=1
            wanted=r.expected(site,regs,[1]);actual,steps,_=r.run(t,site[0],regs,[1],limit=20000)
            success=actual[0]==254 if wanted is None else actual==wanted[0]
            if not success:
                actual,steps,trace=r.run(t,site[0],regs,[1],limit=20000,trace=True)
                entry={'site_index':i,'site':site,'positive':pos,'steps':steps,'clean_exit':r.clean_dispatch(*actual),'zero_run':max(map(len,site[0].split('1'))),'visits218':any(x[1]==218 for x in trace),'actual':r.describe(actual),'expected':r.describe(wanted[0]) if wanted else None,'registers':regs,'spares':[1]}
                bad.append(entry)
                if len(bad)==1 or (entry['visits218'] and entry['zero_run']<=6 and not any(x['visits218'] and x['zero_run']<=6 for x in bad[:-1])):
                    (r.OUT/(name+'_witness_'+str(i)+('_positive' if pos else '')+'.json')).write_text(json.dumps(dict(entry,trace=trace),indent=2)+'\n')
            count+=1
    report={'name':name,'scope':'Finite regression: primary registers zero except positive decrement argument one; spare suffix [1], extra gap zero','cases':count,'failures':len(bad),'seconds':time.monotonic()-began,'first_failure':bad[0] if bad else None,'first_failure_visiting_218_with_input_zero_run_at_most6':next((x for x in bad if x['visits218'] and x['zero_run']<=6),None)}
    (r.OUT/(name+'_finite_failures.json')).write_text(json.dumps(bad,indent=2)+'\n')
    print(json.dumps(report),flush=True);reports.append(report)
(r.OUT/'finite_regression_summary.json').write_text(json.dumps(reports,indent=2)+'\n')
