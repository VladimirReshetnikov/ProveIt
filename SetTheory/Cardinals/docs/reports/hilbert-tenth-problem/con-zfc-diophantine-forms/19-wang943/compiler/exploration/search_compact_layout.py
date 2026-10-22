from itertools import combinations
import json
k=943;a=10;cp=[list(range(o,o+a)) for o in (1023,1013,1003,983)]
non=set(range(k))|set(sum(cp,[]))|{1063,1064}
L=15625
for anchors in [(1095,1096,2195,3296),(1095,1096,2196,3298),(1065,1066,2130,3197),(1065,1066,2131,3199)]:
 u1,u2,v1,v2=anchors; E=non|set(anchors); Emax=max(E); D={x-y for x in E for y in E}
 ad=v2-v1
 if [(x,y) for x in E for y in (x+ad,) if y in E] != [(v1,v2)]:
  print('bad anchors',anchors);continue
 shifts=[v1-u1,v2-u2]
 for H in range(Emax+max(shifts)+1,Emax+max(shifts)+101):
  bare=[30,H+20]+shifts
  targets=cp[1]+[H+x for x in cp[0]]+[v1,v2]
  expected=[{x} for x in cp[3]]+[{x} for x in cp[2]]+[{u1},{u2}]
  if any({t-v for v in bare if t-v in E}!=e for t,e in zip(targets,expected)):continue
  if any(({t-H} if t-H in E else set())!=({cp[0][i-10]} if 10<=i<20 else set()) for i,t in enumerate(targets)):continue
  if any(({t} if t in E else set())!=({t} if i<10 or i>=20 else set()) for i,t in enumerate(targets)):continue
  forbidden=set(x+s for x in E for s in bare)
  options=[T for T in range(Emax+1,L-Emax) if T not in forbidden and all(T-t not in D for t in targets)]
  for T1,T2 in combinations(options,2):
   if (T2-T1)%4!=2 or T2-T1 in D:continue
   dc=sum(pow(2,s,5) for s in bare)%5
   unit=(2*dc-pow(2,H,5))%5
   if not unit:continue
   print('FOUND',dict(anchors=anchors,H=H,T1=T1,T2=T2,bare=bare,L=L,unit=unit,options=len(options)));raise SystemExit
 print('none',anchors)
