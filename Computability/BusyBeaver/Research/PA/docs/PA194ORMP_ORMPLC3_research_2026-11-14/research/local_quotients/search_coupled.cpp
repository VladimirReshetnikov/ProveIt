#include <bits/stdc++.h>
using namespace std;
struct Act {int w,d,n;};
Act T[10000][2];bool have[10000];vector<int> states;vector<pair<int,int>> inc[10000];
int ali(int x,int a,int b){return x==a?b:x;}
// Return 0 on failure, 1 on the desired output, 2 if an as-yet unspecified row is needed.
int sim(int a,int b,int old,int bit,int hist,int dir,Act acts[2],int assigned,int cap){
 Act expect=T[old][bit];expect.n=ali(expect.n,a,b);int lo=min(0,-dir),hi=max(0,-dir);
 int tape[3]={-1,-1,-1};tape[1]=bit;tape[1-dir]=hist;int want[3];copy(tape,tape+3,want);want[1]=expect.w;
 int q=b,pos=0;
 for(int t=0;t<cap;t++){
  if(pos<lo||pos>hi||!have[q])return 0;
  int sym=tape[pos+1];Act ac;
  if(q==b){if(!(assigned&(1<<sym)))return 2;ac=acts[sym];}else ac=T[q][sym];
  tape[pos+1]=ac.w;pos+=ac.d;q=ali(ac.n,a,b);
  if(q==expect.n&&pos==expect.d&&equal(tape,tape+3,want))return 1;
 }
 return 0;
}
bool check(int a,int b,int bit,Act acts[2],int assigned,int cap){for(int old:{a,b})for(auto [hist,dir]:inc[old])if(!sim(a,b,old,bit,hist,dir,acts,assigned,cap))return false;return true;}
int main(int argc,char**argv){
 if(argc<2)return 1;ifstream f(argv[1]);int q,r,w,n;char d;
 while(f>>q>>r>>w>>d>>n){T[q][r]={w,d=='R'?1:-1,n};have[q]=true;auto p=make_pair(w,d=='R'?1:-1);if(find(inc[n].begin(),inc[n].end(),p)==inc[n].end())inc[n].push_back(p);}
 for(int q=0;q<10000;q++)if(have[q])states.push_back(q);
 int start=argc>2?atoi(argv[2]):74,cap=argc>3?atoi(argv[3]):64;
 long long pairs=0,tried=0,pre=0;int found=0;
 for(int i=0;i<(int)states.size();i++)for(int j=i+1;j<(int)states.size();j++){
  int a=states[i],b=states[j];if(a==start||b==start||inc[a].empty()||inc[b].empty())continue;pairs++;
  vector<Act> cand;
  for(int n:states)if(n!=a)for(int w:{0,1})for(int d:{-1,1})cand.push_back({w,d,n});
  bool skip=false;
  for(int bit=0;bit<2;bit++)for(auto c:inc[a])if(find(inc[b].begin(),inc[b].end(),c)!=inc[b].end()){
    Act x=T[a][bit],y=T[b][bit];if(x.w!=y.w||x.d!=y.d||ali(x.n,a,b)!=ali(y.n,a,b)){skip=true;break;}
  }
  if(skip)continue;
  vector<Act> good[2];Act acts[2];
  for(int bit=0;bit<2;bit++)for(Act ac:cand){acts[bit]=ac;pre++;if(check(a,b,bit,acts,1<<bit,cap))good[bit].push_back(ac);}
  for(Act ac0:good[0])for(Act ac1:good[1]){
   acts[0]=ac0;acts[1]=ac1;tried++;
   if(check(a,b,0,acts,3,cap)&&check(a,b,1,acts,3,cap)){
    cout<<"MERGE "<<a<<" "<<b<<"\n";
    for(int bit=0;bit<2;bit++){Act ac=acts[bit];cout<<bit<<" "<<ac.w<<" "<<(ac.d==1?'R':'L')<<" "<<ac.n<<"\n";}
    found++;
   }
  }
 }
 cerr<<"states="<<states.size()<<" pairs="<<pairs<<" partial_candidates="<<pre<<" assignments="<<tried<<" merges="<<found<<"\n";
}
