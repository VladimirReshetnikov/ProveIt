from reconstruct import *
count=0
for J in (0,1):
 E=n+J.bit_count();rr=[n*S.bit_count()+minor_count((J,S)) for S in range(1,8)]
 Q=s.Matrix(7,7,lambda i,j:4*rr[i]*rr[j]-5*E*(n*minor_count((i+1,j+1))+minor_count((J,i+1,j+1))))
 cc=[-1,-1,1,-1,1,1]
 for i in range(7):
  need(s.expand(Q[i,6]-sum(cc[j]*Q[i,j] for j in range(6)))==0,('R feature relation',J,i));count+=1
for core in profiles():
 pop={i:Ns[i-1] for i in range(1,8)}
 for row in range(3):
  mask=sum(((v>>row)&1)<<j for j,v in enumerate(core))
  if mask:pop[mask]+=1
 total=sum(pop.values());dd=[sum(v for m,v in pop.items() if m>>i&1) for i in range(3)]
 direct=endpoint(core,(('B',0),('B',1),('B',2)))
 ie=falling_choose(total,3)-sum(falling_choose(total-d,3) for d in dd)+sum(falling_choose(pop[i],3) for i in (1,2,4))-sum(falling_choose(pop[1<<i],2)*sum(v for mask,v in pop.items() if mask&(7^(1<<i))==7^(1<<i)) for i in range(3))
 need(s.expand(direct-ie)==0,('q-all formula',core));count+=1
out={'all_pass':True,'R_feature_relations':14,'q_all_Hall_reconstructions':61}
(OUT/'relations_audit.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
