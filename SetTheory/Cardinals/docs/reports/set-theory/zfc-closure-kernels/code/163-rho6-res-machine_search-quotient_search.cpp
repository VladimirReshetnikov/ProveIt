#include <bits/stdc++.h>
using namespace std;
struct Act{int w,d,z;};
struct Context{int word;vector<int>trace;};
struct Cas{int word;const vector<int>*trace;};
int enc(int q,int h,int w){return (q*15+h+7)*32768+w;}
int main(int argc,char**argv){
 ifstream in(argv[1]);int N;in>>N;vector<int> labels(N+1);for(int i=0;i<N;i++)in>>labels[i];labels[N]=254;vector<array<Act,2>>T(N);for(auto&rr:T)for(auto&a:rr)in>>a.w>>a.d>>a.z;vector<vector<Context>>I(N);for(auto&v:I){int n;in>>n;v.resize(n);for(auto&x:v)in>>x.word;}
 auto start=chrono::steady_clock::now();long long ntrace=0;
 for(int old=0;old<N;old++)for(auto&x:I[old]){int q=old,h=0,w=x.word;unordered_set<int>seen;for(int tick=0;tick<97;tick++){
  if(h < -7 || h > 7 || q>=N)break;int key=enc(q,h,w);if(!seen.insert(key).second)break;Act a=T[q][(w>>(h+7))&1];w=(w&~(1<<(h+7)))|(a.w<<(h+7));h+=a.d;q=a.z;if(h>=-7&&h<=7)x.trace.push_back(enc(q,h,w));}
 sort(x.trace.begin(),x.trace.end());x.trace.erase(unique(x.trace.begin(),x.trace.end()),x.trace.end());ntrace+=x.trace.size();}
 cerr<<"precomputed traces "<<ntrace<<"\n";
 vector<Act>acts;for(int w:{0,1})for(int d:{-1,1})for(int z=0;z<=N;z++)acts.push_back({w,d,z});

 mt19937 gen(216);long long specs=0,surv=0,pairs=0;
 for(int a=0;a<N;a++)for(int c=a+1;c<N;c++){
  auto phi=[&](int q){return q==c?a:q;};pairs++;
  vector<Cas>cs[2];for(int old:{a,c})for(auto&x:I[old])cs[(x.word>>7)&1].push_back({x.word,&x.trace});
  for(int bit=0;bit<2;bit++)shuffle(cs[bit].begin(),cs[bit].end(),gen);
  vector<int>hits[2];
  for(int bit=0;bit<2;bit++)for(int action=0;action<(int)acts.size();action++){
   Act ac=acts[action];if(ac.z==c)continue;bool success=true;specs++;
   for(const Cas&x:cs[bit]){
    int word=(x.word&~(1<<7))|(ac.w<<7);int q=phi(ac.z),h=ac.d;bool ok=false;
    for(int tick=0;tick<96;tick++){
     if(h < -7 || h > 7)break;int key=enc(q,h,word);if(binary_search(x.trace->begin(),x.trace->end(),key)||(q==a&&binary_search(x.trace->begin(),x.trace->end(),enc(c,h,word)))){ok=true;break;}
     if(q>=N)break;int scanned=(word>>(h+7))&1;if(q==a&&scanned!=bit){ok=true;break;}
     Act z=q==a?ac:T[q][scanned];word=(word&~(1<<(h+7)))|(z.w<<(h+7));h+=z.d;q=phi(z.z);
    }
    if(!ok){success=false;break;}
   }
   if(success)hits[bit].push_back(action);
  }

  for(int i:hits[0])for(int j:hits[1]){
   array<Act,2>choices{acts[i],acts[j]};bool good=true;
   for(int bit=0;bit<2;bit++){
    for(const Cas&x:cs[bit]){
     int q=a,h=0,word=x.word;bool ok=false;
     for(int tick=0;tick<97;tick++){
      if(h < -7 || h > 7)break;
      if(tick){int key=enc(q,h,word);if(binary_search(x.trace->begin(),x.trace->end(),key)||(q==a&&binary_search(x.trace->begin(),x.trace->end(),enc(c,h,word)))){ok=true;break;}}
      if(q>=N)break;int scanned=(word>>(h+7))&1;
      Act z=q==a?choices[scanned]:T[q][scanned];word=(word&~(1<<(h+7)))|(z.w<<(h+7));h+=z.d;q=phi(z.z);
     }
     if(!ok){good=false;break;}
    }
    if(!good)break;
   }
   if(good){surv++;cout<<"FOLD "<<labels[a]<<" "<<labels[c]<<" rows";for(auto ac:choices)cout<<" "<<ac.w<<" "<<ac.d<<" "<<labels[ac.z];cout<<"\n"<<flush;}
  }
  if(pairs%1000==0)cerr<<"pairs "<<pairs<<" survivors "<<surv<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
 }
 cerr<<"pairs "<<pairs<<" row-specs "<<specs<<" folds "<<surv<<" seconds "<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"\n";
}
