// Four history-tagged controls replaced by two representatives and one shared
// selector. The current cell tags the pair; the previous cell tags its member.
// Exact two-cell symbolic simulation, arbitrary exterior tape untouched.
#include <bits/stdc++.h>
using namespace std;struct A{int w,d,n;bool operator==(const A&o)const{return w==o.w&&d==o.d&&n==o.n;}};
struct P{int a,b,c;};struct T{int q,hist,read,tq,th,tw;};
int main(int argc,char**argv){if(argc<2)return 2;map<int,array<A,2>>old;vector<int>states;ifstream f(argv[1]);int q,b,w,n;char d;while(f>>q>>b>>w>>d>>n){if(!old.count(q))states.push_back(q);old[q][b]={w,d=='R'?1:-1,n};}
 map<int,set<pair<int,int>>>inc;for(auto&[q,rs]:old)for(auto a:rs)inc[a.n].insert({a.w,a.d});vector<int>ls,rs;for(int q:states)if(q!=74){if(inc[q]==set<pair<int,int>>{{0,1}})ls.push_back(q);if(inc[q]==set<pair<int,int>>{{1,1}})rs.push_back(q);}
 vector<P>pairs;for(int a:ls)for(int b:rs){bool e0=old[a][0]==old[b][0],e1=old[a][1]==old[b][1];if(e0!=e1)pairs.push_back({a,b,e0?0:1});}
 long long configs=0,trials=0,combos=0,hits=0;
 for(int ia=0;ia<(int)pairs.size();ia++)for(int ib=ia+1;ib<(int)pairs.size();ib++){
  array<P,2>pp={pairs[ia],pairs[ib]};if(pp[0].c!=pp[1].c)continue;set<int>roles={pp[0].a,pp[0].b,pp[1].a,pp[1].b};if(roles.size()!=4)continue;int common=pp[0].c,read=1-common;
  for(int rev=0;rev<4;rev++){array<int,2>keep,drop;map<int,int>alias;for(int i=0;i<2;i++){keep[i]=(rev>>i&1)?pp[i].b:pp[i].a;drop[i]=(rev>>i&1)?pp[i].a:pp[i].b;alias[drop[i]]=keep[i];}auto rho=[&](int q){return alias.count(q)?alias[q]:q;};
   for(int use=0;use<2;use++)for(int tag=0;tag<2;tag++){
    configs++;int selector=drop[use],removed=drop[1-use];auto rows=old;rows.erase(removed);for(auto&[q,rr]:rows)for(auto&a:rr)a.n=rho(a.n);for(int i=0;i<2;i++)rows[keep[i]][read]={tag^i,-1,selector};
    vector<T>tests[2];for(int h=0;h<2;h++)for(int i=0;i<2;i++){int orig=h?pp[i].b:pp[i].a;auto a=old[orig][read];tests[h].push_back({keep[i],h,read,rho(a.n),a.d,a.w});}
    int known=0;array<int,2>targets;
    auto check=[&](T tc)->int{int q=tc.q,h=0,tape=(tc.hist|(tc.read<<1));
     for(int st=0;st<=63;st++){
      if(st&&q==tc.tq&&h==tc.th&&tape==(tc.hist|(tc.tw<<1)))return 1;
      if(st==63||h<-1||h>0||!rows.count(q))return 0;int b=tape>>(h+1)&1;A a;
      if(q==selector){if(!(known>>b&1))return 2;a={b,1,targets[b]};}else a=rows[q][b];
      tape=(tape&~(1<<(h+1)))|(a.w<<(h+1));h+=a.d;q=a.n;
     }return 0;};
    vector<int>choices[2];for(int h=0;h<2;h++){known=1<<h;for(int p:states)if(p!=removed){trials++;targets[h]=p;bool ok=true;for(T t:tests[h])if(!check(t)){ok=false;break;}if(ok)choices[h].push_back(p);}}
    known=3;for(int p0:choices[0])for(int p1:choices[1]){combos++;targets={p0,p1};bool ok=true;for(int h=0;h<2;h++)for(T t:tests[h])if(check(t)!=1)ok=false;if(!ok)continue;
     hits++;cout<<"{\"pairs\":[["<<pp[0].a<<','<<pp[0].b<<"],["<<pp[1].a<<','<<pp[1].b<<"]],\"common\":"<<common<<",\"keeps\":["<<keep[0]<<','<<keep[1]<<"],\"drops\":["<<drop[0]<<','<<drop[1]<<"],\"selector\":"<<selector<<",\"removed\":"<<removed<<",\"tag0\":"<<tag<<",\"providers\":["<<p0<<','<<p1<<"]}"<<endl;
    }
   }
  }
 }
 cerr<<"DONE pairs "<<pairs.size()<<" configurations "<<configs<<" row_trials "<<trials<<" joint_pairs "<<combos<<" hits "<<hits<<endl;
}
