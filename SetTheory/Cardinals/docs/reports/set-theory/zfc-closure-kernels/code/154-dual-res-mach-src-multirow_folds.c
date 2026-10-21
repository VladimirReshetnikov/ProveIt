#define _POSIX_C_SOURCE 200809L
#define main original_fold_main
#include "whole_primitive_folds.c"
#undef main

/* Partial-execution enumeration of several arbitrary action rows.
   Unknown actions stop a run with UNKNOWN, never with a proved PASS.
   Every complete survivor is checked against all supplied finite frames. */
enum {MAXEDIT=8,MAXACT=4*(NQ+1)};
int nedit,eqs[MAXEDIT],ebs[MAXEDIT],assigned[MAXEDIT],rowid[NQ][2];
int removed=-1,redirect=-1,ssq[MAXFR],ssh[MAXFR],ssdone[MAXFR];
unsigned char sst[MAXFR][MAXSZ];
Row domains[MAXEDIT][MAXACT];int ndomain[MAXEDIT],order[MAXEDIT];
int cases[MAXFR],ncase;unsigned long long nodes=0,limitnodes=100000000ULL,multihits=0;
FILE *mhits;clock_t mbeg;int aborted=0;

int mendpoint(int k,int q,int h,unsigned char *t){
 Frame *f=&frames[k];
 int want=f->q==254?254:dispatch;
 if(q!=want)return 0;
 if(general_frames)return q==254||generalized_matches(k,h+gauge,t);
 return h==f->h-(q==254?0:gauge)&&expected_matches(f,t);
}
int mtest(int k){
 tests++;if(ssdone[k])return ssdone[k]==1;
 Frame *f=&frames[k];unsigned char t[MAXSZ];memcpy(t,sst[k],sz);
 int q=ssq[k],h=ssh[k],lim=4*f->ticks+1600;
 for(int step=0;step<lim;step++){
  if(q==254||q==removed||!live[q]||h<0||h>=sz)return 0;
  int id=rowid[q][t[h]];
  if(id>=0&&!assigned[id])return 2+id;
  Row a=tab[q][t[h]];t[h]=a.w;h+=a.d;q=a.q;ticks++;
  if(q==254||(q==dispatch&&clean_dispatch(h+gauge,t))){
   if(q!=254&&internal_macro_frame(f,h+gauge,t))continue;
   return mendpoint(k,q,h,t);
  }
 }
 return 0;
}
int all_partial(void){
 for(int c=0;c<ncase;c++)if(!mtest(cases[c]))return 0;
 for(int k=0;k<nf;k++)if(!mtest(k)){remember_case(cases,&ncase,k);return 0;}
 return 1;
}
void report_hit(void){
 multihits++;fprintf(mhits,"%d %d",removed,redirect);
 for(int j=0;j<nedit;j++){Row a=tab[eqs[j]][ebs[j]];fprintf(mhits," %d %d %d %d %d",eqs[j],ebs[j],a.w,a.d,a.q);}
 fprintf(mhits,"\n");fflush(mhits);
 printf("FOUND_MULTI %llu nodes=%llu\n",multihits,nodes);fflush(stdout);
}
void search_depth(int depth){
 if(aborted)return;
 if(depth==nedit){report_hit();return;}
 int j=order[depth];assigned[j]=1;
 for(int a=0;a<ndomain[j];a++){
  if(++nodes>limitnodes){aborted=1;break;}
  tab[eqs[j]][ebs[j]]=domains[j][a];
  if(all_partial())search_depth(depth+1);
  if(aborted)break;
 }
 assigned[j]=0;
 if(depth<=1){printf("PROGRESS_MULTI depth=%d nodes=%llu hits=%llu seconds=%.2f\n",depth,nodes,multihits,(double)(clock()-mbeg)/CLOCKS_PER_SEC);fflush(stdout);}
}
int main(int argc,char **argv){
 if(argc!=5)return 2;
 setenv("VERIFY_ONLY","1",1);int rc=original_fold_main(argc,argv);unsetenv("VERIFY_ONLY");if(rc)return rc;
 const char *rr=getenv("MULTI_ROWS");if(!rr)return 20;
 char *end;
 while(*rr){
  long q=strtol(rr,&end,10);if(end==rr)break;rr=end;
  long b=strtol(rr,&end,10);if(end==rr)return 21;rr=end;
  if(nedit>=MAXEDIT||q<0||q>=NQ||!live[q]||b<0||b>1)return 22;
  eqs[nedit]=q;ebs[nedit++]=b;
 }
 removed=getenv("REMOVE_STATE")?atoi(getenv("REMOVE_STATE")):-1;
 redirect=getenv("REDIRECT_STATE")?atoi(getenv("REDIRECT_STATE")):-1;
 if(getenv("MAX_NODES"))limitnodes=strtoull(getenv("MAX_NODES"),NULL,10);
 memset(rowid,-1,sizeof(rowid));
 for(int j=0;j<nedit;j++)rowid[eqs[j]][ebs[j]]=j;
 if(redirect>=0)for(int i=0;i<ns;i++)for(int b=0;b<2;b++)if(tab[states[i]][b].q==removed){
  Row *a=&tab[states[i]][b];if(drop_tag_mode==1||(drop_tag_mode==2&&a->d==-1)||(drop_tag_mode==3&&a->d==1))a->w^=1;a->q=redirect;
 }
 for(int k=0;k<nf;k++){
  Frame *f=&frames[k];unsigned char *t=sst[k];memcpy(t,f->initial,sz);
  int q=dispatch,h=off-gauge,lim=4*f->ticks+1600;
  ssdone[k]=2;
  for(int step=0;step<lim;step++){
   if(q==254||q==removed||!live[q]||h<0||h>=sz)break;
   if(rowid[q][t[h]]>=0){ssdone[k]=0;ssq[k]=q;ssh[k]=h;break;}
   Row a=tab[q][t[h]];t[h]=a.w;h+=a.d;q=a.q;
   if(q==254||(q==dispatch&&clean_dispatch(h+gauge,t))){
    if(q!=254&&internal_macro_frame(f,h+gauge,t))continue;
    ssdone[k]=mendpoint(k,q,h,t)?1:2;break;
   }
  }
  if(ssdone[k]==2){printf("FIXED_PREFIX_FAILURE %d\n",k);return 23;}
 }
 mhits=fopen(argv[4],"w");mbeg=clock();
 for(int j=0;j<nedit;j++){
  for(int k=0;k<2;k++){int id=witness[eqs[j]][ebs[j]][k];if(id>=0)remember_case(cases,&ncase,id);}
 }
 for(int j=0;j<nedit;j++){
  assigned[j]=1;
  for(int w=0;w<2;w++)for(int d=-1;d<=1;d+=2)for(int zi=0;zi<=ns;zi++){
   int z=zi==ns?254:states[zi];if(z==removed)continue;
   Row a={w,d,z};
   if(getenv("PIN_BASE_ACTIONS")){Row orig=base[eqs[j]][ebs[j]];if(a.w!=orig.w||a.d!=orig.d||a.q!=orig.q)continue;}
   tab[eqs[j]][ebs[j]]=a;
   if(all_partial())domains[j][ndomain[j]++]=a;
  }
  assigned[j]=0;order[j]=j;
  printf("DOMAIN %d row=%d/%d allowed=%d seconds=%.2f\n",j,eqs[j],ebs[j],ndomain[j],(double)(clock()-mbeg)/CLOCKS_PER_SEC);fflush(stdout);
 }
 for(int a=0;a<nedit;a++)for(int b=a+1;b<nedit;b++)if(ndomain[order[b]]<ndomain[order[a]]){int j=order[a];order[a]=order[b];order[b]=j;}
 search_depth(0);
 printf("DONE_MULTI status=%s edits=%d nodes=%llu hits=%llu tests=%llu ticks=%llu seconds=%.2f\n",aborted?"BUDGET_REACHED":"COMPLETE",nedit,nodes,multihits,tests,ticks,(double)(clock()-mbeg)/CLOCKS_PER_SEC);
 fclose(mhits);return 0;
}
