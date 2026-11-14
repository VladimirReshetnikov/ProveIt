#define main ordered_search_main
#include "ordered_search.cpp"
#undef main
int main(int argc,char**argv){
 if(argc<4)return 2;use_compatible=true;
 ifstream in(argv[1]);int nb;in>>nb;for(int i=0;i<nb;i++){int q;in>>q;base.push_back(q);fixedstate[q]=true;for(int b=0;b<2;b++)in>>rows[q][b].w>>rows[q][b].d>>rows[q][b].n;}
 ifstream ia(argv[2]);int na;ia>>na;for(int j=0;j<na;j++){int q;Attr a;ia>>q>>a.h>>a.l>>a.m>>a.mi>>a.inc;a.len=1;a.bad=0;leafattrs[q]=a;}
 E e;int nt;in>>nt;int id,n,rt;in>>id>>n>>rt;vector<int>values(n);for(int i=0;i<n;i++){T t;in>>t.op>>t.a>>t.b>>t.c;values[i]=t.op?e.pair(values[t.a],values[t.b]):leaf(t.a);}int root=values[rt];vector<int>word;e.flatten(root,word);if(word.size()!=190)throw runtime_error("expected190tokens");
 const int lens[]={17,19,16,16,16,19,7};array<vector<int>,7>parts;int lo=18;for(int h=0;h<7;h++){parts[h]=vector<int>(word.begin()+lo,word.begin()+lo+lens[h]);lo+=lens[h];}
 int best=999,cases=0,hits=0;array<int,7>order={0,1,2,3,4,5,6};string pref=argv[3];ofstream csv(pref+".csv");csv<<"case,gamma,order,score,nodes,folds,penalty\n";
 do{for(int gamma:{98,12,166}){
  vector<int>fresh(word.begin(),word.begin()+18);for(int h:order){for(int t:parts[h])fresh.push_back(h==6&&physical(t)==98?leaf(gamma):t);}fresh.insert(fresh.end(),word.begin()+128,word.end());int nr=e.reword(root,fresh);auto v=scored(e,nr,order);cases++;
  csv<<cases<<','<<gamma<<',';for(int h:order)csv<<h;csv<<','<<v.score<<','<<v.n<<','<<v.fold<<','<<v.pen<<'\n';
  if(v.score<best){best=v.score;e.save(nr,pref+".best.grammar.json");cout<<"BEST "<<best<<" n "<<v.n<<" folds "<<v.fold<<" penalty "<<v.pen<<" case "<<cases<<endl;}
  if(v.score<=60&&hits<300){e.save(nr,pref+".seed"+to_string(hits++)+".grammar.json");}
 }}while(next_permutation(order.begin(),order.end()));cout<<"DONE cases "<<cases<<" best "<<best<<" seeds "<<hits<<endl;
}
