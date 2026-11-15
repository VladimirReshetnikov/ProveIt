#include <bits/stdc++.h>
using namespace std;
struct Act {int w,d,n;};
Act T[10000][2]; bool have[10000];vector<int> states;vector<pair<int,int>> inc[10000];
int alias(int x,int a,int b){return x==a?b:x;}
bool sim(int a,int b,int old,int bit,int hist,int dir,Act first,int cap){
  Act expect=T[old][bit];expect.n=alias(expect.n,a,b);
  int lo=min(0,-dir),hi=max(0,-dir);
  int tape[3]={-1,-1,-1};tape[1]=bit;tape[1-dir]=hist;
  int want[3];copy(tape,tape+3,want);want[1]=expect.w;
  int q=b,pos=0;
  for(int t=0;t<cap;t++){
    Act ac;
    if(t==0)ac=first;
    else {if(q==b||!have[q]||pos<lo||pos>hi)return false;ac=T[q][tape[pos+1]];}
    if(pos<lo||pos>hi)return false;
    tape[pos+1]=ac.w;pos+=ac.d;q=alias(ac.n,a,b);
    if(q==expect.n && pos==expect.d && equal(tape,tape+3,want))return true;
  }
  return false;
}
bool works(int a,int b,int bit,Act first,int cap){
 for(int old:{a,b})for(auto [hist,dir]:inc[old])if(!sim(a,b,old,bit,hist,dir,first,cap))return false;
 return true;
}
int main(int argc,char**argv){
 if(argc<2)return 1;ifstream f(argv[1]);int q,r,w,n;char d;
 while(f>>q>>r>>w>>d>>n){T[q][r]={w,d=='R'?1:-1,n};have[q]=true;auto p=make_pair(w,d=='R'?1:-1);if(find(inc[n].begin(),inc[n].end(),p)==inc[n].end())inc[n].push_back(p);}
 for(int q=0;q<10000;q++)if(have[q])states.push_back(q);
 int start=argc>2?atoi(argv[2]):74;int cap=argc>3?atoi(argv[3]):32;
 long long pairs=0,tried=0;int found=0;
 for(int i=0;i<(int)states.size();i++)for(int j=i+1;j<(int)states.size();j++){
  int a=states[i],b=states[j];if(a==start||b==start||inc[a].empty()||inc[b].empty())continue;pairs++;
  vector<Act> opts[2];
  for(int bit=0;bit<2;bit++){
   vector<Act> cand{T[a][bit],T[b][bit]};
   for(int n:states)if(n!=a&&n!=b)for(int w:{0,1})for(int d:{-1,1})cand.push_back({w,d,n});
   set<tuple<int,int,int>> seen;
   for(Act ac:cand){ac.n=alias(ac.n,a,b);if(!seen.emplace(ac.w,ac.d,ac.n).second)continue;tried++;if(works(a,b,bit,ac,cap))opts[bit].push_back(ac);}
   if(opts[bit].empty())break;
  }
  if(opts[0].empty()||opts[1].empty())continue;
  cout<<"MERGE "<<a<<" "<<b<<" options "<<opts[0].size()<<" "<<opts[1].size()<<"\n";
  for(int bit=0;bit<2;bit++)for(Act ac:opts[bit])cout<<bit<<" "<<ac.w<<" "<<(ac.d==1?'R':'L')<<" "<<ac.n<<"\n";
  found++;
 }
 cerr<<"states="<<states.size()<<" pairs="<<pairs<<" candidates="<<tried<<" merges="<<found<<"\n";
}
