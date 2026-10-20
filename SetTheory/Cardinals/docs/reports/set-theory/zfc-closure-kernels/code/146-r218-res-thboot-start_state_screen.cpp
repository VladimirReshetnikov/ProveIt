// Exact finite blank-start screen over existing start states. Discovery only.
#include <bits/stdc++.h>
using namespace std;
struct Action {int w,d,q;};
Action table_[512][2];
bool live[512];
int main(int argc,char**argv){
 if(argc<2)return 2;
 ifstream input(argv[1]);string line;
 while(getline(input,line)){
  if(line.empty()||line[0]=='#')continue;
  istringstream s(line);int q,b,w,z;char d;s>>q>>b>>w>>d>>z;
  table_[q][b]={w,d=='R'?1:-1,z};live[q]=true;
 }
 long long limit=argc>2?atoll(argv[2]):2000000;
 int wanted[]={1,1,1,4,1,1,4,1,1};
 int hits=0;
 for(int start=0;start<512;start++)if(live[start]){
  vector<unsigned char> tape(2*limit+20,0);
  int origin=limit+10,q=start,h=origin,mn=origin,mx=origin,count=0,dispatches=0;
  auto value=[&](int p){return tape[p];};
  long long tick=0;string reason="bound";
  for(;tick<limit;tick++){
   if(q==84){
    dispatches++;
    if(count>=18 && mn==h-1 && tape[h-1] && !tape[h]){
     int header=h;
     while(header<=mx&&!tape[header])header++;
     bool ok=header>=h+64 && header<=mx && !tape[header+1];
     int p=header+1;
     vector<int> spares;
     for(int k=0;k<9&&ok;k++){
      if(value(p)!=0 || value(p+1)!=1){ok=false;break;}
      p++;int n=0;while(value(p)){n++;p++;}
      if(n!=wanted[k])ok=false;
     }
     while(ok&&p<=mx){
      if(value(p)!=0||value(p+1)!=1){ok=false;break;}
      p++;int n=0;while(value(p)){n++;p++;}
      spares.push_back(n-1);
     }
     if(ok&&!spares.empty()&&p==mx+1){
      hits++;cout<<"HIT start "<<start<<" tick "<<tick<<" head "<<h-origin
        <<" header "<<header-origin<<" gap "<<header-h-64<<" spares "<<spares.size()
        <<" ones "<<count<<" values";
      for(int x:spares)cout<<" "<<x;cout<<"\n";
      cout<<"TAPE";for(int p=mn;p<=mx;p++)if(tape[p])cout<<" "<<p-origin;cout<<"\n";
      reason="hit";break;
     }
    }
   }
   if(!live[q]){reason="halt";break;}
   int b=value(h);
   if(q==35&&b==0&&h>mx){reason="runaway35";break;}
   if((q==6||q==75)&&b==0&&h>mx){reason="right_blank_scan";break;}
   if(q==1&&b==0&&h<mn){reason="left_blank_scan";break;}
   Action a=table_[q][b];
   if(a.w!=b){
    tape[h]=a.w;count+=a.w?1:-1;
    if(a.w){if(count==1)mn=mx=h;else{mn=min(mn,h);mx=max(mx,h);}}
    else if(count){while(!tape[mn])mn++;while(!tape[mx])mx--;}
    else mn=mx=h;
   }
   h+=a.d;q=a.q;
  }
  cerr<<"END "<<start<<" "<<tick<<" "<<reason<<" q "<<q<<" head "<<h-origin<<" ones "<<count<<" dispatches "<<dispatches<<"\n";
 }
 cerr<<"HITS "<<hits<<"\n";
}
