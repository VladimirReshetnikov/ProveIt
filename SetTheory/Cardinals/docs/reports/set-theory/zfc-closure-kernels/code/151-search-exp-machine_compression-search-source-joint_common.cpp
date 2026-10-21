#include <bits/stdc++.h>
using namespace std;struct A{int w,d,z;};struct C{int q,m;vector<tuple<int,int,int>>path;};struct Test{C*c;vector<uint64_t>goals;bool oh;int q,h,bit;};const int R=7,F=97;A O[303][2],N[303][2];vector<int>Q;vector<C>cs[303];int kp,dr,sh;map<int,vector<Test>>cache;
uint64_t key(int q,int h,int m){return(uint64_t(q)<<21)|(uint64_t(h+16)<<15)|m;}
vector<Test>&get(int q){if(!cache.count(q)){vector<Test>v;for(auto&c:cs[q]){int h=q==dr?sh:0;Test t{&c,{},false,q==dr?kp:q,h,(c.m>>(h+R))&1};for(auto[x,y,m]:c.path){t.oh|=x==254;t.goals.push_back(key(x==dr?kp:x,y+(x==dr?sh:0),m));}sort(t.goals.begin(),t.goals.end());v.push_back(move(t));}cache[q]=move(v);}return cache[q];}
int run(Test&t,int defer=-1){int q=t.q,h=t.h,m=t.c->m;uint64_t seen[F];int sn=0;for(int tick=0;tick<F;tick++){if(q==254||h< -R||h>R)return 0;auto v=key(q,h,m);for(int j=0;j<sn;j++)if(seen[j]==v)return 0;seen[sn++]=v;int b=(m>>(h+R))&1;if(q==kp&&b==defer)return 2;auto a=N[q][b];m=(m&~(1<<(h+R)))|(a.w<<(h+R));h+=a.d;q=a.z;if(q==254)return t.oh;if(binary_search(t.goals.begin(),t.goals.end(),key(q,h,m)))return 1;}return 0;}

int main(int argc,char**argv){ifstream f(argv[1]);int n;f>>n;for(int i=0;i<n;i++){int q;f>>q;Q.push_back(q);for(int b=0;b<2;b++)f>>O[q][b].w>>O[q][b].d>>O[q][b].z;}int nc;f>>nc;for(int i=0;i<nc;i++){int q,m;f>>q>>m;C c{q,m,{}};int st=q,h=0,t=m;for(int j=0;j<F;j++){if(st==254||h< -R||h>R)break;auto a=O[st][(t>>(h+R))&1];t=(t&~(1<<(h+R)))|(a.w<<(h+R));h+=a.d;st=a.z;c.path.emplace_back(st,h,t);}cs[q].push_back(move(c));}for(int q:Q)if(cs[q].size()>1)swap(cs[q][1],cs[q].back());
long long total=0,partial=0,hits=0;int pairs=0;auto begin=chrono::steady_clock::now();sh=0;
for(int i=0;i<(int)Q.size();i++)for(int j=i+1;j<(int)Q.size();j++){kp=Q[i];dr=Q[j];int common=-1,ncommon=0;for(int b:{0,1}){auto a=O[kp][b],c=O[dr][b];if(a.z==dr)a.z=kp;if(c.z==dr)c.z=kp;if(a.w==c.w&&a.d==c.d&&a.z==c.z){common=b;ncommon++;}}if(ncommon!=1)continue;pairs++;int freebit=1-common;cache.clear();for(int q:Q)for(int b:{0,1}){N[q][b]=O[q][b];if(N[q][b].z==dr)N[q][b].z=kp;}vector<Test*>tests;for(int q:{dr,kp})for(auto&t:get(q))if(t.bit==freebit)tests.push_back(&t);auto targets=Q;targets.erase(find(targets.begin(),targets.end(),dr));targets.push_back(254);
for(int hq:Q){if(hq==kp||hq==dr)continue;for(int hb:{0,1}){A saved=N[hq][hb];for(int fw:{0,1})for(int fd:{-1,1}){N[kp][freebit]={fw,fd,hq};vector<Test*>bad;
for(int hw:{0,1})for(int hd:{-1,1})for(int hz:targets){total++;N[hq][hb]={hw,hd,hz};bool pass=true;for(Test*t:bad)if(!run(*t)){pass=false;break;}if(!pass)continue;for(Test*t:tests)if(!run(*t)){pass=false;if(bad.size()<128&&find(bad.begin(),bad.end(),t)==bad.end())bad.push_back(t);break;}if(!pass)continue;partial++;
for(auto&t:get(hq)){if(((t.c->m>>R)&1)!=hb)continue;if(!run(t)){pass=false;if(bad.size()<128&&find(bad.begin(),bad.end(),&t)==bad.end())bad.push_back(&t);break;}}if(!pass)continue;
hits++;cout<<"HIT "<<kp<<" "<<dr<<" common "<<common<<" actions "<<N[kp][0].w<<" "<<N[kp][0].d<<" "<<N[kp][0].z<<" "<<N[kp][1].w<<" "<<N[kp][1].d<<" "<<N[kp][1].z<<" helper "<<hq<<" "<<hb<<" "<<hw<<" "<<hd<<" "<<hz<<endl;
ofstream out(string(argv[2])+"/joint-common-"+to_string(kp)+"-"+to_string(dr)+"-"+to_string(hits)+".tm");out<<"#! start 0\n";for(int q:Q)if(q!=dr)for(int b:{0,1}){auto a=N[q][b];out<<q<<" "<<b<<" "<<a.w<<" "<<(a.d==1?'R':'L')<<" "<<a.z<<"\n";}
}
}N[hq][hb]=saved;}}
cerr<<"PAIR "<<pairs<<" "<<kp<<" "<<dr<<" common "<<common<<" total "<<total<<" partial "<<partial<<" hits "<<hits<<" time "<<chrono::duration<double>(chrono::steady_clock::now()-begin).count()<<endl;
}
cerr<<"DONE "<<pairs<<" "<<total<<" "<<partial<<" "<<hits<<endl;}
