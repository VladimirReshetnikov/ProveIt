#include <stdio.h>
#include <stdlib.h>
#include <time.h>
/* Minimal GMP ABI declarations for the installed 64-bit Linux library. */
typedef struct { int alloc, size; unsigned long *limbs; } Z;
extern void __gmpz_init(Z*); extern void __gmpz_set_ui(Z*,unsigned long);
extern void __gmpz_set(Z*,const Z*); extern void __gmpz_addmul(Z*,const Z*,const Z*);
extern char *__gmpz_get_str(char*,int,const Z*);
int main(int argc,char **argv){int N=atoi(argv[1]); Z **c=calloc(N+1,sizeof(Z*)); FILE *f=fopen(argv[2],"w");
 c[0]=calloc(N+2,sizeof(Z));for(int k=0;k<N+2;k++){__gmpz_init(&c[0][k]);__gmpz_set_ui(&c[0][k],1);}fprintf(f,"0 1\n");
 for(int n=1;n<=N;n++){ c[n]=calloc(N-n+2,sizeof(Z)); for(int k=0;k<N-n+2;k++)__gmpz_init(&c[n][k]);
 for(int k=1;k<=N-n+1;k++){__gmpz_set(&c[n][k],&c[n][k-1]);for(int i=0;i<n;i++)__gmpz_addmul(&c[n][k],&c[i][k],&c[n-1-i][k+1]);}
 char *s=__gmpz_get_str(NULL,10,&c[n][1]);fprintf(f,"%d %s\n",n,s);free(s);if(n%100==0){fflush(f);fprintf(stderr,"%d %.1f seconds\n",n,(double)clock()/CLOCKS_PER_SEC);}}
 fclose(f);return 0;}
