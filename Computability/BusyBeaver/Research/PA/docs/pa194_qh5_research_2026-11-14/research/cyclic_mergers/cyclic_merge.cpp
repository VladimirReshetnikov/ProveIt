#include <bits/stdc++.h>
using namespace std;
struct A{int w,d,n;};
struct Case{int q,bit,pat;};
int main(int argc,char**argv){
 if(argc<4)return 2;ifstream in(argv[1]);int K=atoi(argv[2]),W=2*K+1,N=1<<W,MASK=N-1,LIM=atoi(argv[3]);
 A rows[3000][2]{};bool ex[3000]{};int q,b,w,n;char d;vector<int>states;string line;
 while(getline(in,line)){istringstream s(line);if(!(s>>q>>b>>w>>d>>n))continue;rows[q][b]={w,d=='R'?1:-1,n};if(!ex[q])states.push_back(q);ex[q]=1;}
 if(states.empty()){cerr<<"ERROR empty input table"<<endl;return 2;}
 vector<vector<uint8_t>>reach(3000,vector<uint8_t>(N));queue<pair<int,int>>todo;
 auto add=[&](int q,int p){if(ex[q]&&!reach[q][p]){reach[q][p]=1;todo.emplace(q,p);}};
 int startq=(*min_element(states.begin(),states.end())==0 && *max_element(states.begin(),states.end())==(int)states.size()-1)?0:74;
 for(int p=0;p<N;p++)add(startq,p);
 while(!todo.empty()){auto[q,p]=todo.front();todo.pop();A a=rows[q][p>>K&1];p=(p&~(1<<K))|(a.w<<K);if(a.d==1){int v=p>>1;add(a.n,v);add(a.n,v|(1<<(W-1)));}else{int v=(p<<1)&MASK;add(a.n,v);add(a.n,v|1);}}
 if(argc>4){ifstream pin(argv[4]);map<int,vector<uint8_t>>s;int rq,rp;while(pin>>rq>>rp){if(!s.count(rq))s[rq]=vector<uint8_t>(N);s[rq][rp]=1;}for(auto&[rq,v]:s)reach[rq]=v;}
 vector<A>actions;for(int n:states)for(int w:{0,1})for(int d:{-1,1})actions.push_back({w,d,n});int M=actions.size();
 long long pairs=0,zerook=0,full=0;auto start=chrono::steady_clock::now();
 for(int ai=0;ai<(int)states.size();ai++)for(int bi=ai+1;bi<(int)states.size();bi++){
 int a=states[ai],r=states[bi];if(a==startq||r==startq)continue;pairs++;
 vector<Case>cases[2];for(int p=0;p<N;p++)for(int q:{a,r})if(reach[q][p])cases[p>>K&1].push_back({q,p>>K&1,p});
 // partial result: 1 complete, 0 failed, 2 other action needed.
 auto test=[&](const Case&c,int x,int y){
  A old=rows[c.q][c.bit];int tq=old.n==a?r:old.n,th=old.d,tp=(c.pat&~(1<<K))|(old.w<<K);
  int q=r,h=0,p=c.pat;
  uint64_t seen[160];int seenN=0;
  for(int st=0;st<=LIM;st++){
   if(st&&q==tq&&h==th&&p==tp)return 1;
   if(h< -K||h>K||!ex[q]||st==LIM)return 0;
   uint64_t key=((uint64_t(q)<<32)|((h+K)<<24)|p);for(int i=0;i<seenN;i++)if(seen[i]==key)return 0;if(seenN<160)seen[seenN++]=key;
   int bit=p>>(h+K)&1;A act;
   if(q==r){int idx=bit?y:x;if(idx<0)return 2;act=actions[idx];}else act=rows[q][bit];
   p=(p&~(1<<(h+K)))|(act.w<<(h+K));h+=act.d;q=act.n==a?r:act.n;
  }return 0;
 };
 vector<int>firstOrder;for(int j=0;j<M;j++)if(actions[j].n!=a)firstOrder.push_back(j);
 vector<Case>hard=cases[0];
 for(int x:firstOrder){bool ok=true;vector<Case>unresolved;
  for(auto c:hard){int v=test(c,x,-1);if(!v){ok=false;break;}if(v==2)unresolved.push_back(c);}
  if(!ok)continue;zerook++;
  unresolved.insert(unresolved.end(),cases[1].begin(),cases[1].end());
  for(int y:firstOrder){bool good=true;for(auto c:unresolved)if(test(c,x,y)!=1){good=false;break;}
   if(!good)continue;full++;
   // all cases again final exact check
   for(int bit=0;bit<2;bit++)for(auto c:cases[bit])if(test(c,x,y)!=1)abort();
   cout<<"{\"remove\":"<<a<<",\"keep\":"<<r<<",\"actions\":[["<<actions[x].w<<','<<actions[x].d<<','<<actions[x].n<<"],["<<actions[y].w<<','<<actions[y].d<<','<<actions[y].n<<"]]}"<<endl;
  }
 }
 if(pairs%100==0)cerr<<"pairs="<<pairs<<" partial="<<zerook<<" full="<<full<<" seconds="<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<endl;
 }
 cerr<<"DONE pairs="<<pairs<<" partial="<<zerook<<" full="<<full<<endl;
}
