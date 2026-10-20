// Joint122/0,137/0 exact-window confluence and blank-start screen.
#include <bits/stdc++.h>
using namespace std;
struct A {int w,d,q;};
struct C {int q,h;unsigned bits;bool operator==(C const&o)const{return q==o.q&&h==o.h&&bits==o.bits;}};
A T[512][2];bool live[512];
bool step(C&c,A x,A y,bool mutate){
 if(c.h < -7||c.h>7||!live[c.q])return false;
 int b=(c.bits>>(c.h+7))&1;
 A a=mutate&&b==0&&c.q==122?x:mutate&&b==0&&c.q==137?y:T[c.q][b];
 c.bits=(c.bits&~(1u<<(c.h+7)))|(a.w<<(c.h+7));c.h+=a.d;c.q=a.q;return true;
}
bool boot(A x,A y,int &ticks,int&head,int&header,int&spares,int&count){
 int limit=1500000,origin=limit+10,q=0,h=origin,mn=origin,mx=origin;
 vector<unsigned char> tape(2*origin+10,0);count=0;
 int wanted[]={1,1,1,4,1,1,4,1,1};
 for(int tick=0;tick<limit;tick++){
  if(q==84&&count>=18&&mn==h-1&&tape[h-1]&&!tape[h]){
   int hd=h;while(hd<=mx&&!tape[hd])hd++;
   bool ok=hd>=h+64&&hd<=mx&&!tape[hd+1];int p=hd+1;
   for(int k=0;k<9&&ok;k++){
    if(tape[p]!=0||tape[p+1]!=1){ok=false;break;}
    p++;int n=0;while(tape[p]){n++;p++;}if(n!=wanted[k])ok=false;
   }
   int ns=0;while(ok&&p<=mx){
    if(tape[p]!=0||tape[p+1]!=1){ok=false;break;}
    p++;while(tape[p])p++;ns++;
   }
   if(ok&&ns&&p==mx+1){ticks=tick;head=h-origin;header=hd-origin;spares=ns;return true;}
  }
  if(!live[q])return false;
  int b=tape[h];
  if(q==35&&b==0&&h>mx)return false;
  if((q==6||q==75)&&b==0&&h>mx)return false;
  if(q==1&&b==0&&h<mn)return false;
  A a=b==0&&q==122?x:b==0&&q==137?y:T[q][b];
  if(a.w!=b){tape[h]=a.w;count+=a.w?1:-1;
   if(a.w){if(count==1)mn=mx=h;else{mn=min(mn,h);mx=max(mx,h);}}
   else if(count){while(!tape[mn])mn++;while(!tape[mx])mx--;}
   else mn=mx=h;
  }
  h+=a.d;q=a.q;
 }
 return false;
}
int main(int argc,char**argv){
 if(argc!=3)return 2;
 string line;ifstream file(argv[1]);
 while(getline(file,line)){if(line.empty()||line[0]=='#')continue;istringstream s(line);int q,b,w,z;char d;s>>q>>b>>w>>d>>z;T[q][b]={w,d=='R'?1:-1,z};live[q]=true;}
 vector<C> inputs;vector<vector<C>> goals;ifstream in(argv[2]);
 while(getline(in,line)){istringstream s(line);int q;unsigned bits;s>>q>>bits;if((q!=122&&q!=137)||((bits>>7)&1))continue;
  C c{q,0,bits};inputs.push_back(c);vector<C> g;
  for(int k=0;k<40;k++){if(!step(c,{},{},false))break;g.push_back(c);}goals.push_back(g);
 }
 vector<A> actions;for(int q=0;q<512;q++)if(live[q])for(int w=0;w<2;w++)for(int d:{-1,1})actions.push_back({w,d,q});
 cerr<<"INPUTS "<<inputs.size()<<" PAIRS "<<actions.size()*actions.size()<<"\n";
 int hits=0,success=0;long long checks=0;
 for(A x:actions)for(A y:actions){bool good=true;int longest=0;
  for(int i=0;i<(int)inputs.size()&&good;i++){
   C c=inputs[i];bool joined=false;
   for(int k=1;k<=128;k++){checks++;if(!step(c,x,y,true))break;
    if(find(goals[i].begin(),goals[i].end(),c)!=goals[i].end()){joined=true;longest=max(longest,k);break;}
   }
   if(!joined)good=false;
  }
  if(good){hits++;cout<<"NEUTRAL "<<x.w<<" "<<x.d<<" "<<x.q<<" / "<<y.w<<" "<<y.d<<" "<<y.q<<" steps "<<longest<<"\n"<<flush;
   int ticks,head,header,spares,count;
   if(boot(x,y,ticks,head,header,spares,count)){success++;cout<<"BOOT_SUCCESS "<<x.w<<" "<<x.d<<" "<<x.q<<" / "<<y.w<<" "<<y.d<<" "<<y.q<<" ticks "<<ticks<<" head "<<head<<" header "<<header<<" spares "<<spares<<" ones "<<count<<"\n"<<flush;}
  }
 }
 cerr<<"DONE neutral "<<hits<<" boot "<<success<<" checks "<<checks<<"\n";
}
