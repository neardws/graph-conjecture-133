/* Independent re-implementation of the finite search behind Lemma 5.7.
   Target: connected G, no 4-cycle subgraph, no induced P7, contains a triangle,
           L(v)=2d(v)-3t(v) >= 4 for all v, no two adjacent vertices of degree 2.
   Search: start from a triangle H.  At a node H:
     - deficient vertex v (L_H(v) < 4): G has a neighbour of v outside H.
     - adjacent pair a,b with d_H(a)=d_H(b)=2: G has a neighbour of a or b outside H.
     If some such "decision" exists, branch over every legal U (N(z) in H) meeting the decision set.
     Decision chosen fail-first: the one with fewest legal children (the authors use a supplied certificate).
     If none exists (H satisfies both local conditions), record H and branch over all nonempty legal U.
   Legal U: H+z has no 4-cycle and no induced P7.
   Reports: nodes, leaves, max order, per-order counts, and every "unrestricted" node (graph6) for iso check.
   Usage: lemma57 [initial-graph6]   (default: triangle)
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint32_t set;
#define MAXV 32
static long nodes=0, leaves=0, unrestricted=0; static int maxorder=0; static long perorder[MAXV+1];
static FILE *uf;
static int popc(set x){return __builtin_popcount(x);}

static int found;
static void dfs(const set *A,int last,set B,int len){
    if(len>=7){found=1;return;}
    set cand=A[last]&~B, Bn=B|A[last]|(1u<<last);
    for(set t=cand;t&&!found;t&=t-1) dfs(A,__builtin_ctz(t),Bn,len+1);
}
static int hasP7(const set *A,int n){ found=0; for(int s=0;s<n&&!found;s++) dfs(A,s,0,1); return found; }

static void g6(const set *A,int n,char *buf){
    int k=0; buf[k++]=63+n; int bits=0,val=0;
    for(int j=1;j<n;j++) for(int i=0;i<j;i++){ val=(val<<1)|((A[i]>>j)&1); if(++bits==6){buf[k++]=63+val;bits=0;val=0;} }
    if(bits){val<<=(6-bits);buf[k++]=63+val;} buf[k]=0;
}

/* enumerate all legal nonempty U */
typedef struct { set *U; int cnt, cap; } ulist;
static void push(ulist *L,set u){ if(L->cnt==L->cap){L->cap=L->cap?2*L->cap:64; L->U=realloc(L->U,L->cap*sizeof(set));} L->U[L->cnt++]=u; }
static void recU(const set *A,int n,int v,set U,set forb,ulist *L){
    if(v==n){
        if(!U) return;
        set B[MAXV]; for(int i=0;i<n;i++) B[i]=A[i]|(((U>>i)&1)?(1u<<n):0); B[n]=U;
        if(!hasP7(B,n+1)) push(L,U);
        return;
    }
    recU(A,n,v+1,U,forb,L);
    if(!((forb>>v)&1)){
        set f=forb; for(int w=0;w<n;w++) if(w!=v&&(A[w]&A[v])) f|=1u<<w;
        recU(A,n,v+1,U|(1u<<v),f,L);
    }
}

static void search(set *A,int n){
    nodes++; perorder[n]++; if(n>maxorder) maxorder=n;
    if(n>=MAXV-1){ fprintf(stderr,"order cap reached\n"); exit(2); }
    ulist L={0,0,0}; recU(A,n,0,0,0,&L);
    /* candidate decisions */
    set dec[2*MAXV*MAXV]; int nd=0;
    for(int v=0;v<n;v++){
        int d=popc(A[v]); int t=0; for(set q=A[v];q;q&=q-1) t+=popc(A[__builtin_ctz(q)]&A[v]); t/=2;
        if(2*d-3*t<4) dec[nd++]=1u<<v;
    }
    for(int a=0;a<n;a++) if(popc(A[a])==2) for(set q=A[a];q;q&=q-1){int b=__builtin_ctz(q); if(b>a&&popc(A[b])==2) dec[nd++]=(1u<<a)|(1u<<b);}
    set X=0; /* 0 = unrestricted */
    if(nd>0){
        int best=-1,bc=1<<30;
        for(int i=0;i<nd;i++){ int c=0; for(int k=0;k<L.cnt;k++) if(L.U[k]&dec[i]) c++; if(c<bc){bc=c;best=i;} }
        X=dec[best];
    } else {
        unrestricted++; char buf[64]; g6(A,n,buf); fprintf(uf,"%s\n",buf);
    }
    int kids=0;
    for(int k=0;k<L.cnt;k++){
        set U=L.U[k]; if(X && !(U&X)) continue;
        set B[MAXV]; for(int i=0;i<n;i++) B[i]=A[i]|(((U>>i)&1)?(1u<<n):0); B[n]=U;
        kids++; search(B,n+1);
    }
    if(!kids) leaves++;
    free(L.U);
}

int main(int argc,char**argv){
    set A[MAXV]={0}; int n=3;
    uf=fopen(argc>2?argv[2]:"unrestricted.g6","w");
    if(argc>1 && strcmp(argv[1],"-")){
        const unsigned char*p=(const unsigned char*)argv[1]; n=*p++-63; int bits=0,val=0;
        for(int j=1;j<n;j++) for(int i=0;i<j;i++){ if(!bits){val=*p++-63;bits=6;} bits--; if((val>>bits)&1){A[i]|=1u<<j;A[j]|=1u<<i;} }
    } else { A[0]=6;A[1]=5;A[2]=3; }
    search(A,n);
    fclose(uf);
    printf("nodes=%ld leaves=%ld unrestricted=%ld maxorder=%d\n",nodes,leaves,unrestricted,maxorder);
    printf("visited nodes by order:"); for(int k=0;k<=maxorder;k++) if(perorder[k]) printf(" %d:%ld",k,perorder[k]); printf("\n");
    return 0;
}
