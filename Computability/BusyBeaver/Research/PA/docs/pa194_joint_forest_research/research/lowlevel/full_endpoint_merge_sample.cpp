#include <bits/stdc++.h>
using namespace std;
using U=__uint128_t;
struct A {int w,d,n;};struct C {int id,br,bz,extra,kind,reg;U start,goal;};
A base[3000][2],row[3000][2];bool ex[3000];vector<int> qs,eligible;vector<C>cs;int SK[9]={51,36,25,48,32,33,22,55,60},sk[3000];int merged=-1;long long calls=0,ticks=0;
U setbit(U v,int h,int w){U m=(U)1<<(h+16);return w?v|m:v&~m;}
U pathmask(string s,int extra=0){U m=(U)1<<15;m|=(U)1<<(64+extra);for(int i=0;i<(int)s.size();i++)if(s[i]=='1')m|=(U)1<<(16+i);return m;}
// 0 failure/cutoff, 1 exact endpoint, 2/3 unknown row0/1.
int run(const C& c,int mode=0){calls++;U tape=c.start;int q=84,h=0,bo=49,kind=0,reg=-1;
 for(int st=0;st<2048;st++){
  ticks++;if(st && ((c.kind==4&&q==254)||(c.kind!=4&&q==84&&h==0&&bo==49+c.extra&&kind==c.kind&&reg==c.reg&&tape==c.goal)))return 1;
  if(q==254||!ex[q]||h < -15 || h>bo)return 0;
  if(h==bo){
   if(kind==0&&sk[q]>=0){reg=sk[q];kind=1;q=reg==0?1:3;h--;continue;}
   if(kind==1&&reg<9){
    if(q==64){q=40;kind=2;h--;continue;}
    if(q==0&&c.br==reg){
     if(c.bz){q=97;kind=0;reg=-1;h--;}
     else{q=40;kind=3;tape=setbit(tape,bo,1);bo++;}
     continue;
    }
   }
   auto a=row[q][0];if(a.w<0)return 2;
   if(a.w==0&&a.d==-1){q=a.n;h--;continue;}return 0;
  }
  int b=(tape>>(h+16))&1;auto a=row[q][b];if(a.w<0)return 2+b;
  tape=setbit(tape,h,a.w);h+=a.d;q=a.n;
 }
 return 0;
}
int main(int argc,char**argv){if(argc<4)return 2;fill(sk,sk+3000,-1);for(int i=0;i<9;i++)sk[SK[i]]=i;ifstream f(argv[1]);int q,b,w,n;char d;while(f>>q>>b>>w>>d>>n){if(!ex[q])qs.push_back(q);ex[q]=true;base[q][b]=row[q][b]={w,d=='R'?1:-1,n};}ifstream cf(argv[2]);C c;string src,tgt;while(cf>>c.id>>c.br>>c.bz>>c.extra>>c.kind>>c.reg>>src>>tgt){c.start=pathmask(src);c.goal=pathmask(tgt,c.extra);cs.push_back(c);}ifstream ef(argv[3]);while(ef>>q)eligible.push_back(q);
 for(auto&x:cs){if(run(x)!=1){cerr<<"Baseline mismatch "<<x.id<<"\n";return 3;}}
 cerr<<"Baseline OK "<<cs.size()<<" calls "<<calls<<" ticks "<<ticks<<"\n";
 auto t0=chrono::steady_clock::now();long long pairs=0,trials=0,products=0,hits=0;int first=argc>4?stoi(argv[4]):0,last=argc>5?stoi(argv[5]):1000000;
 for(int ia=0;ia<(int)eligible.size();ia++)for(int ib=ia+1;ib<(int)eligible.size();ib++){
  int a=eligible[ia],b=eligible[ib];pairs++;if(pairs<=first||pairs>last)continue;
  memcpy(row,base,sizeof row);ex[a]=false;for(int p:qs)for(int bit=0;bit<2;bit++)if(row[p][bit].n==a)row[p][bit].n=b;
  row[b][0].w=row[b][1].w=-1;
  vector<int>groups[2];bool ok=true;for(int i=0;i<(int)cs.size();i++){int res=run(cs[i]);if(!res){ok=false;break;}if(res>1)groups[res-2].push_back(i);}if(!ok){ex[a]=true;continue;}
  mt19937 rng(a*3000+b);shuffle(groups[0].begin(),groups[0].end(),rng);shuffle(groups[1].begin(),groups[1].end(),rng);vector<A>surv[2];
  for(int bit=0;bit<2;bit++){
   for(int wr=0;wr<2;wr++)for(int dir:{-1,1})for(int p:qs)if(p!=a){
    A ac{wr,dir,p};row[b][bit]=ac;trials++;bool good=true;
    for(int k=0;k<min(24,(int)groups[bit].size());k++){int i=groups[bit][k],res=run(cs[i]);if(!res){good=false;if(k){groups[bit].erase(groups[bit].begin()+k);groups[bit].insert(groups[bit].begin(),i);}break;}}
    if(good)surv[bit].push_back(ac);
   }
   row[b][bit].w=-1;
  }
  vector<int>test=groups[0];test.insert(test.end(),groups[1].begin(),groups[1].end());
  for(auto ac0:surv[0])for(auto ac1:surv[1]){
   products++;row[b][0]=ac0;row[b][1]=ac1;bool good=true;
   for(int k=0;k<(int)test.size();k++){int i=test[k];if(run(cs[i])!=1){good=false;if(k){test.erase(test.begin()+k);test.insert(test.begin(),i);}break;}}
   if(good){hits++;cout<<a<<' '<<b<<' '<<ac0.w<<' '<<ac0.d<<' '<<ac0.n<<' '<<ac1.w<<' '<<ac1.d<<' '<<ac1.n<<endl;}
  }
  ex[a]=true;
  if(pairs%100==0)cerr<<"pairs "<<pairs<<" trials "<<trials<<" products "<<products<<" hits "<<hits<<" calls "<<calls<<" ticks "<<ticks<<" secs "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<endl;
 }
 cerr<<"DONE pairs "<<pairs<<" trials "<<trials<<" products "<<products<<" hits "<<hits<<" calls "<<calls<<" ticks "<<ticks<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-t0).count()<<endl;
}
