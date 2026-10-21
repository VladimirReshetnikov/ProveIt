#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>
using namespace std;
struct Act{int w,d,z;};
int main(int argc,char**argv){
 if(argc!=5)return 2;string table=argv[1],out=argv[2];int r=stoi(argv[3]);bool arbitrary=stoi(argv[4]);
 if(r<0||r>10)return 3;ifstream in(table);int N=0,start=0;if(!(in>>N>>start)||N!=215)return 4;vector<vector<Act>>T(N,vector<Act>(2));int q,b,w,d,z;
 while(in>>q>>b>>w>>d>>z)T[q][b]={w,d,z};
 uint32_t W=1u<<(2*r+1),mask=W-1;vector<uint8_t>seen(N*W,0);vector<uint32_t>todo;bool halt=false;
 auto add=[&](uint32_t id){if(!seen[id]){seen[id]=1;todo.push_back(id);}};
 if(arbitrary)for(uint32_t a=0;a<W;a++)add(start*W+a);else add(start*W);
 for(size_t i=0;i<todo.size();i++){
  uint32_t id=todo[i],q=id/W,v=id%W;auto a=T[q][(v>>r)&1];uint32_t wr=(v&~(1u<<r))|(a.w<<r);
  if(a.z==N){halt=true;continue;}
  if(a.d==1){uint32_t nx=wr>>1;add(a.z*W+nx);add(a.z*W+(nx|(1u<<(2*r))));}
  else{uint32_t nx=(wr<<1)&mask;add(a.z*W+nx);add(a.z*W+(nx|1));}
 }
 ofstream bin(out+".bits",ios::binary);for(size_t i=0;i<seen.size();i+=8){uint8_t a=0;for(int j=0;j<8&&i+j<seen.size();j++)a|=seen[i+j]<<j;bin.put(a);}bin.close();
 ofstream json(out+".json");json<<"{\"radius\":"<<r<<",\"initial_mode\":\""<<(arbitrary?"arbitrary_window":"blank_window")<<"\",\"working_states\":"<<N<<",\"windows_per_state\":"<<W<<",\"explicit_domain\":"<<N*W<<",\"reachable_abstract_configurations\":"<<todo.size()<<",\"halt_may_be_reached\":"<<(halt?"true":"false")<<",\"state_window_counts\":[";
 int states=0,rowslive=0;vector<int>deadstates;vector<pair<int,int>>deadrows;
 for(int q=0;q<N;q++){uint32_t count=0;bool live[2]={};for(uint32_t v=0;v<W;v++)if(seen[q*W+v]){count++;live[(v>>r)&1]=true;}
  if(q)json<<',';json<<count;if(count)states++;else deadstates.push_back(q);for(int b=0;b<2;b++)if(live[b])rowslive++;else deadrows.push_back({q,b});}
 json<<"],\"reachable_state_count\":"<<states<<",\"reachable_read_row_count\":"<<rowslive<<",\"dead_states_dense\":[";for(size_t i=0;i<deadstates.size();i++){if(i)json<<',';json<<deadstates[i];}json<<"],\"dead_rows_dense\":[";for(size_t i=0;i<deadrows.size();i++){if(i)json<<',';json<<'['<<deadrows[i].first<<','<<deadrows[i].second<<']';}json<<"]}\n";
 cout<<out<<" domain="<<N*W<<" reachable="<<todo.size()<<" states="<<states<<" rows="<<rowslive<<" dead="<<deadrows.size()<<endl;
}
