#include <bits/stdc++.h>
using namespace std;struct A{int w,d,z;};struct C{int q,m;vector<tuple<int,int,int>>path;};struct Test{C*c;vector<uint64_t>goals;bool oh;int q,h,bit;};const int R=7,F=97;A O[303][2],N[303][2];vector<int>Q;vector<C>cs[303];int kp,dr,sh;map<int,vector<Test>>cache;
uint64_t key(int q,int h,int m){return(uint64_t(q)<<21)|(uint64_t(h+16)<<15)|m;}
vector<Test>&get(int q){if(!cache.count(q)){vector<Test>v;for(auto&c:cs[q]){int h=q==dr?sh:0;Test t{&c,{},false,q==dr?kp:q,h,(c.m>>(h+R))&1};for(auto[x,y,m]:c.path){t.oh|=x==254;t.goals.push_back(key(x==dr?kp:x,y+(x==dr?sh:0),m));}sort(t.goals.begin(),t.goals.end());v.push_back(move(t));}cache[q]=move(v);}return cache[q];}
int run(Test&t,int defer=-1){int q=t.q,h=t.h,m=t.c->m;uint64_t seen[F];int sn=0;for(int tick=0;tick<F;tick++){if(q==254||h< -R||h>R)return 0;auto v=key(q,h,m);for(int j=0;j<sn;j++)if(seen[j]==v)return 0;seen[sn++]=v;int b=(m>>(h+R))&1;if(q==kp&&b==defer)return 2;auto a=N[q][b];m=(m&~(1<<(h+R)))|(a.w<<(h+R));h+=a.d;q=a.z;if(q==254)return t.oh;if(binary_search(t.goals.begin(),t.goals.end(),key(q,h,m)))return 1;}return 0;}
int main(int argc,char**argv){kp=atoi(argv[2]);dr=atoi(argv[3]);sh=atoi(argv[4]);ifstream f(argv[1]);int n;f>>n;for(int i=0;i<n;i++){int q;f>>q;Q.push_back(q);for(int b=0;b<2;b++)f>>O[q][b].w>>O[q][b].d>>O[q][b].z;}int nc;f>>nc;for(int i=0;i<nc;i++){int q,m;f>>q>>m;C c{q,m,{}};int s=q,h=0,t=m;for(int j=0;j<F;j++){if(s==254||h< -R||h>R)break;auto a=O[s][(t>>(h+R))&1];t=(t&~(1<<(h+R)))|(a.w<<(h+R));h+=a.d;s=a.z;c.path.emplace_back(s,h,t);}cs[q].push_back(move(c));}for(int q:Q)if(cs[q].size()>1)swap(cs[q][1],cs[q].back());
for(int q:Q)for(int b=0;b<2;b++){N[q][b]=O[q][b];if(N[q][b].z==dr){N[q][b].z=kp;N[q][b].d+=sh;}}
set<pair<int,int>>helpers;for(int q:{kp,dr})for(auto&c:cs[q]){helpers.insert({q,(c.m>>R)&1});for(auto[s,h,m]:c.path)if(s!=254&&h>=-R&&h<=R)helpers.insert({s,(m>>(h+R))&1});}helpers.erase({kp,0});helpers.erase({kp,1});helpers.erase({dr,0});helpers.erase({dr,1});if(argc>5&&string(argv[5])=="all"){helpers.clear();for(int q:Q)if(q!=kp&&q!=dr)for(int b:{0,1})helpers.insert({q,b});}
vector<Test*>tests[2];for(int q:{dr,kp})for(auto&t:get(q))tests[t.bit].push_back(&t);auto targets=Q;targets.erase(find(targets.begin(),targets.end(),dr));targets.push_back(254);long long templates=0,secondspecs=0,partial=0,hits=0;auto begin=chrono::steady_clock::now();
for(int fixed:{0,1})for(auto[hq,hb]:helpers){A saved=N[hq][hb];for(int fw:{0,1})for(int fd:{-1,1}){A fixedact{fw,fd,hq};N[kp][fixed]=fixedact;
for(int hw:{0,1})for(int hd:{-1,1})for(int hz:targets){templates++;A helpact{hw,hd,hz};N[hq][hb]=helpact;bool ok=true;vector<Test*>deferred;
for(Test*t:tests[fixed]){int x=run(*t,1-fixed);if(!x){ok=false;break;}if(x==2)deferred.push_back(t);}if(!ok)continue;partial++;vector<Test*>bad;
for(int ow:{0,1})for(int od:{-1,1})for(int oz:targets){secondspecs++;A other{ow,od,oz};N[kp][1-fixed]=other;bool pass=true;
for(Test*t:bad)if(!run(*t)){pass=false;break;}if(!pass)continue;
for(Test*t:deferred)if(!run(*t)){pass=false;bad.push_back(t);break;}if(!pass)continue;
for(Test*t:tests[1-fixed])if(!run(*t)){pass=false;if(bad.size()<128)bad.push_back(t);break;}if(!pass)continue;
for(auto&t:get(hq))if(!run(t)){pass=false;if(bad.size()<128)bad.push_back(&t);break;}if(!pass)continue;
hits++;cout<<"HIT "<<kp<<" "<<dr<<" "<<sh<<" "<<N[kp][0].w<<" "<<N[kp][0].d<<" "<<N[kp][0].z<<" "<<N[kp][1].w<<" "<<N[kp][1].d<<" "<<N[kp][1].z<<" helper "<<hq<<" "<<hb<<" "<<hw<<" "<<hd<<" "<<hz<<endl;
}
}N[hq][hb]=saved;}
cerr<<"HELPER "<<fixed<<" "<<hq<<"/"<<hb<<" templates "<<templates<<" partial "<<partial<<" second "<<secondspecs<<" hits "<<hits<<" time "<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<endl;
}
cerr<<"DONE "<<kp<<" "<<dr<<" "<<sh<<" "<<helpers.size()<<" "<<templates<<" "<<partial<<" "<<secondspecs<<" "<<hits<<endl;
}
