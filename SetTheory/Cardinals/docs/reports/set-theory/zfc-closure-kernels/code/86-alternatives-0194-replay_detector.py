import json,sys
p=sys.argv[1];data=json.load(open(p));n=data['states'];tab={(q,b):(w,d,s)for q,b,w,d,s in data['table']};rows=[]
for k in range(9):
 lo=-k if k<8 else -7;ones={2}|({-k}if k<8 else set());orig=ones.copy();q=h=t=0;trace=[]
 for t in range(10000):
  if k<8 and q==n and h==-k-1 and ones==orig:break
  if k==8 and q==n+1 and -8<=h<=1 and ones==orig:break
  assert lo<=h<=2,(k,t,q,h,'read exterior')
  assert q<n+1,(k,t,q,h,'wrong exit')
  b=int(h in ones);w,d,s=tab[q,b];trace.append([q,h,b,w,d,s])
  if w:ones.add(h)
  else:ones.discard(h)
  h+=1 if d=='R'else-1;q=s
 else:raise Exception('fuel')
 rows.append({'case':k,'steps':t,'exit_state':q,'exit_head':h,'restored':True,'trace':trace})
out={'status':'PASS','input':p,'cases':rows};print(json.dumps(out,indent=2));open(p+'.replay.json','w').write(json.dumps(out,indent=2)+'\n')
