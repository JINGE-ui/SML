#include<stdlib.h>
#include<stdio.h>
#include<math.h>
#include<string.h>
#include<iostream>
#include<time.h>
using namespace std;
#define TRUE 1
#define FALSE 0
#define YES 1
#define NO 0
#define SATISFIED 0//正文字
#define SHRUNK 1//负文字
#define MAX_CLAUSE_LEN 32 //子句的最大长度
#define SAT 1
#define UNSAT 0
#define UNASSIGNED 2
#define ASSIGN_BRANCHED 1
#define ASSIGN_IMPLIED 2
#define ASSIGN_NONE 0
#define MAX_LEN 500 //从.cnf文件中读取字符串的最大长度
#define MAX_VARS 1500
#define MAX_CLAUSES 6000
typedef struct literal_info{ 
    int is_assigned; //是否已被确定YES/NO
    int n_occur; //该文字所在子句的数目
    int lit_in_clauses[MAX_CLAUSES]; //包含此文字的子句链，下标从0开始，子句索引从0开始
    int lit_in_clauses_locs[MAX_CLAUSES]; //在相应子句中的该文字的位置链，下标从0开始，位置排序从0开始
    int is_unit; //文字k是子句C中唯一未确定时，取YES
    int antecedent_clause; //取C
}literal_info;
literal_info linfo[MAX_VARS][2]; //对于每一变量j的正负文字 j、-j都储存信息

typedef struct clause_info 
{
    int literals[MAX_VARS]; //指向子句所包含的所有文字链,从1开始，下标从0开始
    int current_length; //子句的现在长度
    int original_length; //子句的原始长度
    int is_satisfied; //子句是否满足 YES/NO
    int binary_code; //0-1串，对应于连接的文字链，未确定为1，假值取0
    int current_ucl; //如果是单子句则储存对应的文字，否则取0
}clause_info;
clause_info clauses[MAX_CLAUSES]; 
int n_clauses,r_clauses; //分别为原始和现在子句长度

typedef struct changes_info //记录变化
{
    int clause_index; //每当一个子句满足，被保存
    int literal_index; //一个未确定的文字确定为F时，两者都被保存
}changes_info;
changes_info changes[10000];
unsigned int changes_index; //变化索引
unsigned int n_changes[MAX_VARS][2]; 

typedef struct assign_info //每个变量的赋值信息
{
    int type=UNASSIGNED; //TRUE/FALSE/UNASSIGNED
    int depth; //被赋值的层数
    int decision; //分支选择时确定、被迫确定、未确定
}assign_info;
assign_info assign[MAX_VARS];

int contradictory_unit_clauses,conflicting_literal; //无法满足时
int depth,backtrack_level,max_depth,n_backtracks;
int ic_cnt,impl_clauses[MAX_CLAUSES];//矛盾时储存先行子句
int n_gucl; //构造大小为n_gucl大小的栈，发现单子句时压入栈
int gucl_stack[MAX_CLAUSES]; //单子句栈
int VARS,CLAUSES;
//PUZZLE
int M;
int n;
int a[32][32];
int b[32],c[32]; //都从1起
int remain[880]; //须保留，此数组内必须全为1，才有解
int zhen[32];
int fu[32];
int zong[32];
int know_num;
int flag[32];
int know_var[900];
char puzzleaddr[100];
int n_vars,n_clauses1;
int count,recount;
FILE* fp; //创建.cnf文件
int has(){
    int flag=0,ct=0;
    for(int i=1;i<2*M;i++)
        if(b[i]==1&&b[i+1]==0) {
            b[i]=0,b[i+1]=1;
            flag=i;
            break;
        }
    if(!flag) return 0;
    else {
        for(int k=flag-1;k>=1;k--)
            if(b[k]) ct++;
        for(int i=1;i<=ct;i++)
            b[i]=1;
        for(int i=ct+1;i<flag;i++)
            b[i]=0;
        return 1;
    }
}
void C1(int n,int m,int j){
    for(int i=1;i<=2*M;i++){
        c[i]=i;
    }
    for(int i=1;i<=m;i++)
        b[i]=1;
    c[0]=0;
    b[0]=0;
    for(int i=m+1;i<=2*M;i++){
        b[i]=0;
    }
    for(int i=1;i<=n;i++)
        if(b[i]) fprintf(fp,"%d ",a[c[i]][j]);
        fprintf(fp,"%d\n",0);
    while(has()){
        for(int i=1;i<=n;i++)
            if(b[i]) fprintf(fp,"%d ",a[c[i]][j]);
        fprintf(fp,"%d\n",0);
    }
}
void C2(int n,int m,int j){
    for(int i=1;i<=2*M;i++){
        c[i]=i;
    }
    for(int i=1;i<=m;i++)
        b[i]=1;
    c[0]=0;
    b[0]=0;
    for(int i=m+1;i<=2*M;i++){
        b[i]=0;
    }
    for(int i=1;i<=n;i++)
        if(b[i]) fprintf(fp,"%d ",-a[c[i]][j]);
        fprintf(fp,"%d\n",0);
    while(has()){
        for(int i=1;i<=n;i++)
            if(b[i]) fprintf(fp,"%d ",-a[c[i]][j]);
        fprintf(fp,"%d\n",0);
    }
}
void C3(int n,int m,int j){
    for(int i=1;i<=2*M;i++){
        c[i]=i;
    }
    for(int i=1;i<=m;i++)
        b[i]=1;
    c[0]=0;
    b[0]=0;
    for(int i=m+1;i<=2*M;i++){
        b[i]=0;
    }
    for(int i=1;i<=n;i++)
        if(b[i]) fprintf(fp,"%d ",a[j][c[i]]);
        fprintf(fp,"%d\n",0);
    while(has()){
        for(int i=1;i<=n;i++)
            if(b[i]) fprintf(fp,"%d ",a[j][c[i]]);
        fprintf(fp,"%d\n",0);
    }
}
void C4(int n,int m,int j){
    for(int i=1;i<=2*M;i++){
        c[i]=i;
    }
    for(int i=1;i<=m;i++)
        b[i]=1;
    c[0]=0;
    b[0]=0;
    for(int i=m+1;i<=2*M;i++){
        b[i]=0;
    }
    for(int i=1;i<=n;i++)
        if(b[i]) fprintf(fp,"%d ",-a[j][c[i]]);
        fprintf(fp,"%d\n",0);
    while(has()){
        for(int i=1;i<=n;i++)
            if(b[i]) fprintf(fp,"%d ",-a[j][c[i]]);
        fprintf(fp,"%d\n",0);
    }
}
int jiecheng(int n){
    int sum=1;
    for(int i=1;i<=n;i++){
        sum=sum*i;
    }
    return sum;
}
//DPLL
void SetVar(int v){ //计算F|v，以v为true
    int i;
    int p=abs(v),q=(v>0)?SATISFIED:SHRUNK;
    for(i=0;i<linfo[p][q].n_occur;++i){ //搜索v
        register int j=linfo[p][q].lit_in_clauses[i]; //j是包含v的子句
        if(clauses[j].is_satisfied){
            continue;
        }
        clauses[j].is_satisfied=YES; //将j设为满足
        --r_clauses;
        changes[changes_index++].clause_index=j; //changes数组记录所有的变化
        n_changes[depth][SATISFIED]++;
    }
    q=!q;
    for(i=0;i<linfo[p][q].n_occur;++i){ //搜索-v
        register int j=linfo[p][q].lit_in_clauses[i]; //j是包含-v的子句，记为C
        if(clauses[j].is_satisfied) continue;
        register int k=linfo[p][q].lit_in_clauses_locs[i]; //-v是C的第k个文字
        --clauses[j].current_length; //减小子句长度
        clauses[j].binary_code-=((1<<k));
        changes[changes_index].clause_index=j;
        changes[changes_index++].literal_index=k;
        n_changes[depth][SHRUNK]++; //在depth层确定为FALSE的个数增加
        if(clauses[j].current_length==1){ //C变成了单子句
            int loc=int(log2(clauses[j].binary_code)); //其它文字都为F
            int w=clauses[j].literals[loc]; //单子句中的文字，记为w
            int s=abs(w),t=(w>0)?SATISFIED:SHRUNK;
            linfo[s][t].antecedent_clause=j;
            if(linfo[s][(!t)].is_unit==YES){ //如果-w也是单子句中的文字
                contradictory_unit_clauses=TRUE; //矛盾
                conflicting_literal=w;
            }
            else if(linfo[s][t].is_unit==NO){
                gucl_stack[n_gucl]=clauses[j].current_ucl=w; //将w压入栈中
                linfo[s][t].is_unit=YES;
                ++n_gucl;
            }
       }
    }
    if(depth&&backtrack_level==depth-1)  ++backtrack_level;
    ++depth;
    linfo[p][SATISFIED].is_assigned=YES;
    linfo[p][SHRUNK].is_assigned=YES;
}
void UnSetVar(int v){ //从F|v恢复F
    register int i;
    register int p=abs(v),q=(v>0)?SATISFIED:SHRUNK;
    --depth; //回溯
    if(depth&&backtrack_level==depth){
        --backtrack_level;
    }
    while(n_changes[depth][SHRUNK]){ //含有F的负文字的子句
        --n_changes[depth][SHRUNK];
        register int j=changes[--changes_index].clause_index; //即为C
        register int k=changes[changes_index].literal_index; //即为v
        ++clauses[j].current_length;
        if(clauses[j].current_length==2){ //C之前是一个单子句，现在不是了，将有关信息恢复初值
            int s=abs(clauses[j].current_ucl);
            int t=(clauses[j].current_ucl>0)?SATISFIED:SHRUNK;
            linfo[s][t].is_unit=NO;
            clauses[j].current_ucl=0;
        }
        clauses[j].binary_code+=((1<<k));
    }
    while(n_changes[depth][SATISFIED]){
        --n_changes[depth][SATISFIED];
        register int j=changes[--changes_index].clause_index;
        clauses[j].is_satisfied=NO;
        ++r_clauses;
    }
    linfo[p][SATISFIED].is_assigned=NO;
    linfo[p][SHRUNK].is_assigned=NO;
}
int get_length_of_shortest_unsatisfied_clause(){
    register int i,j,C,type,min=MAX_CLAUSE_LEN;
    if(min==2){
        return min;
    }
    for(i=1;i<=VARS;++i){
        if(assign[i].decision==ASSIGN_NONE){
            for(type=0;type<2;++type){
                for(j=0;j<linfo[i][type].n_occur;++j){
                    C=linfo[i][type].lit_in_clauses[j];
                    if(!clauses[C].is_satisfied&&clauses[C].current_length<min){
                        min=clauses[C].current_length;
                        if(min==2) return 2;
                    }
                }
            }
        }
    }
    return min;
}
void get_MOMS(int x,int k,unsigned int &s,unsigned int &t){
    int j,c;
    s=t=0;
    for(j=0;j<linfo[x][SATISFIED].n_occur;++j){
        c=linfo[x][SATISFIED].lit_in_clauses[j]; //c是包含x的子句
        if(clauses[c].current_length==k){
            s+=1-clauses[c].is_satisfied;
        }
    }
    for(j=0;j<linfo[x][SHRUNK].n_occur;j++){
        c=linfo[x][SHRUNK].lit_in_clauses[j];
        if(clauses[c].current_length==k){
            t+=1-clauses[c].is_satisfied;
        }
    }
}
int GetLiteralMinLen(){
    unsigned int i,k;
    unsigned int max=0,r,s,t;
    int u;
    for(i=1;i<=VARS;i++){
        if(assign[i].decision==ASSIGN_NONE){
            k=get_length_of_shortest_unsatisfied_clause();
            get_MOMS(i,k,s,t); //i是变量，k是当前子句最小长度
            r=(s+1)*(t+1);
            if(r>max){
                max=r;
                if(s>=t){
                    u=i; //取正文字
                }else{
                    u=-i;
                }
            }
        }
    }
    return u;
}
int Getliteralbyorder(){
    for(int i=1;i<=VARS;i++){
        if(assign[i].decision==ASSIGN_NONE){
            return i;
        }
    }
}
int dpll(){ //返回UNSET或SET
    int lucl_stack[VARS-depth];//大小为n_lucl的动态可分配的栈，记录已确定的子句，当dpll返回unset时释放此栈
    unsigned int n_lucl=0;
    while(1){
        if(contradictory_unit_clauses){ //单子句文字必须为T，以此判断上一次决策是否合理
            while(n_lucl){ //是否有单子句被确定了
                UnSetVar(lucl_stack[--n_lucl]);
                register int s=abs(lucl_stack[n_lucl]);
                register int t=lucl_stack[n_lucl]>0?TRUE:FALSE;
                //impl_clauses[ic_cnt++]=linfo[s][t].antecedent_clause;
                assign[s].type=UNASSIGNED;
                assign[s].decision=ASSIGN_NONE;
            }
            contradictory_unit_clauses=FALSE;
            n_gucl=0; //清空单子句栈
            return UNSAT;
        }
        else if(n_gucl){ //是否有单子句，依次强行确定单子句文字
            register int implied_lit=gucl_stack[--n_gucl];
            lucl_stack[n_lucl]=implied_lit;
            n_lucl++;
            assign[abs(implied_lit)].type=implied_lit>0?TRUE:FALSE;
            assign[abs(implied_lit)].decision=ASSIGN_IMPLIED;
            SetVar(implied_lit); //使用该强行确定的文字implied_lit确定剩余公式
        }
        else break;
    }
    //分支策略
    if(!r_clauses){ //子句当前长度为0，返回
        return SAT;
    }
    if(depth>VARS-1) return UNSAT;
    register int v=GetLiteralMinLen(); //分支规则，选择一个v
    assign[abs(v)].type=v>0?TRUE:FALSE;
    assign[abs(v)].depth=depth;
    assign[abs(v)].decision=ASSIGN_BRANCHED;
    SetVar(v);
    if(dpll()){ //递归调用dpll
        return SAT;
    }
    UnSetVar(v);

    assign[abs(v)].type=!assign[abs(v)].type;
    assign[abs(v)].decision=ASSIGN_IMPLIED; //确定类型改为强迫
    SetVar(-v); //将-v设为正确，往右子树递归
    if(dpll()){
        return SAT;
    }
    UnSetVar(-v);
    assign[abs(v)].type=UNASSIGNED;
    assign[abs(v)].decision=ASSIGN_NONE;

    while(n_lucl){
        int z=lucl_stack[--n_lucl];
        UnSetVar(z);
        assign[abs(z)].type=UNASSIGNED;
        assign[abs(z)].decision=ASSIGN_NONE;
    }
    contradictory_unit_clauses=FALSE;
    return UNSAT;
}
char fileaddr[100];
char writeaddr[100];
int legth;
FILE* fpuzzle;
FILE* Fp;
char str[MAX_LEN],cc;
int num_var=0,num_cla=0,num[MAX_LEN/2];//分别为变量和子句数以及数值存储
int flag1;//判断是否已浏览变量数
int literal,literalth,clauseth;
int ans,lit;

void fverify(void){ //逐行输出子句
    for(int i=0;i<CLAUSES;i++){
        for(int j=0;j<clauses[i].original_length;j++){
            printf("%d ",clauses[i].literals[j]);
        }
        printf("\n");
    }
    printf("\n");
}

int main()
{
    char cho;
    int j,i;
    double  duration; 
    clock_t start, finish;
    while(1)
{       
    depth=backtrack_level=n_backtracks=max_depth=0;
    VARS=CLAUSES=0;
    n_clauses = r_clauses = 0;
    changes_index=0;
    memset(linfo,0,sizeof(linfo));
    memset(clauses,0,sizeof(clauses));
    memset(changes,0,sizeof(changes));
    memset(n_changes,0,sizeof(n_changes));
    memset(assign,0,sizeof(assign));
    for(int i=1;i<=MAX_VARS;i++){
        assign[i].type=UNASSIGNED;
    }
    contradictory_unit_clauses=FALSE;
    n_gucl=ic_cnt=0;
    printf("1---puzzle\n2---sat\n3---exit\n");
    cho=getchar();
    if(cho=='2') //SAT
  {
    printf("please input the .cnf file address\n");
    memset(fileaddr,0,sizeof(fileaddr));
    cho=getchar();
    gets(fileaddr);
    cc='a';
    if((Fp=fopen(fileaddr,"r"))==NULL){
        printf("Fail to open the .cnf file!\n");
        continue;
    }
    do{//省略以c开头的备注
        fgets(str,MAX_LEN,Fp);
        cc=str[0];
    }while(cc=='c');
    flag1=0;
    num_var=0,num_cla=0;//分别为变量和子句数
    for(int i=0,j=0;;i++){ //记录VARS和CLAUSES的位数以及数值
        if(str[i]>='a'&&str[i]<='z') continue;
        if(str[i]>='0'&&str[i]<='9'){
            num[j++]=str[i]-'0';
            if(flag1==2) num_var++;
            else num_cla++;
        }else if(str[i]==' '){
            flag1++;
        }else break;
    }
    for(int i=0;i<num_var;i++){
        VARS=10*VARS+num[i];
    }
    for(int i=num_var;i<num_var+num_cla;i++){
        CLAUSES=10*CLAUSES+num[i];
    }
    n_clauses=r_clauses=CLAUSES;
    literal=0,literalth=0,clauseth=0;
    while(clauseth!=CLAUSES&&fscanf(Fp,"%d",&literal)!=EOF){ //子句和文字结构信息的存储
        if(literal!=0){
            literalth++;
            j=(literal>0)?0:1;
            i=abs(literal);
            linfo[i][j].n_occur++;
            linfo[i][j].lit_in_clauses[linfo[i][j].n_occur-1]=clauseth;
            linfo[i][j].lit_in_clauses_locs[linfo[i][j].n_occur-1]=literalth-1;
            clauses[clauseth].literals[literalth-1]=literal;
            clauses[clauseth].current_length++;
            clauses[clauseth].original_length=clauses[clauseth].current_length;
            clauses[clauseth].binary_code=2*clauses[clauseth].binary_code+1;
        }
        else{
            if(literalth==1){
                literal=gucl_stack[n_gucl++]=clauses[clauseth].current_ucl=clauses[clauseth].literals[0];
                j=(literal>0)?0:1;
                i=abs(literal);
                linfo[i][j].is_unit=YES;
                linfo[i][j].antecedent_clause=clauseth;
                clauses[clauseth].current_ucl=literal;
            }
            clauseth++;
            literalth=0;
        }
    }
    fclose(Fp);
    start=clock();
    ans = dpll();
    finish=clock();
    duration = (double)(finish - start) / CLOCKS_PER_SEC;
    duration = 1000*duration;  //化为ms
    printf("the time is %f millisecond\n",duration);
    if(!ans){
        printf("UNSAT\n\n");
        continue;
    }
/*
    flag1=1;
    for(int k=0;k<CLAUSES;k++){
        flag1=0;
        for(int i=0;i<clauses[k].original_length;i++){ //再检验
            lit=clauses[k].literals[i];
            if(lit>0){
                if(assign[lit].type==TRUE){
                    flag1=1;
                    break;
                }
                else{
                    continue;
                }
            }else{
                if(assign[abs(lit)].type==FALSE){
                    flag1=1;
                    break;
                }else{
                    continue;
                }
            }
        }
        if(!flag1){
            printf("UNSAT\n\n");
            break;
        }
    }
    if(!flag1){
        continue;
    }
*/
    else{
        printf("SAT\n");
        memset(writeaddr,0,sizeof(writeaddr));
        strcpy(writeaddr,fileaddr);
        int legth=strlen(fileaddr);
        writeaddr[legth-3]='r';
        writeaddr[legth-2]='e';
        writeaddr[legth-1]='s';
        FILE* fpwrite;
        fpwrite=fopen(writeaddr,"wb");
        if(!fpwrite){
            printf("fail to write .res file!\n");
            continue;
        }
        fprintf(fpwrite,"s //正数表TRUE，负数表FALSE，*表未定\n");
        fprintf(fpwrite,"v\n");
        for(int i=1,type=2;i<=VARS;i++){
            type=assign[i].type;
            if(type==TRUE){
                fprintf(fpwrite,"%d ",i);
            }else if(type==FALSE){
                fprintf(fpwrite,"%d ",-i);
            }else{
                fprintf(fpwrite,"*%d",i);
            }
        }
        fprintf(fpwrite,"\nt %f",duration);
        fclose(fpwrite);
        printf("the result file addres is %s\n\n",writeaddr);
    }
  }
    else if(cho=='1'){  //PUZZLE
        printf("input the puzzle .txt file\n");
        cho=getchar();
        memset(fileaddr,0,sizeof(fileaddr));
        gets(fileaddr);
        memset(puzzleaddr,0,sizeof(puzzleaddr));
        strcpy(puzzleaddr,fileaddr);
        legth=strlen(fileaddr);
        puzzleaddr[legth-3]='c';
        puzzleaddr[legth-2]='n';
        puzzleaddr[legth-1]='f';
        fpuzzle=fopen(fileaddr,"r");
        if(!fpuzzle){
            printf("fail to open the .txt puzzle file\n");
            continue;
        }
        fscanf(fpuzzle,"%d",&M);
        fscanf(fpuzzle,"%d",&know_num);
        n=2*M;
        for(int i=1;i<n+1;i++){
            for(int j=1;j<n+1;j++)
                a[i][j]=(i-1)*n+j;
        }
        n_vars=n*n+n*(n-1)*(3*n+1);
        n_clauses1=4*n*(n-2)+4*n*jiecheng(n)/jiecheng(M-1)/jiecheng(M+1)+n*(n-1)*(10*n+1)+know_num;
        fp=fopen(puzzleaddr,"w");
        if(!fp){
            printf("fail to create puzzle .cnf file\n");
            continue;
        }
        fprintf(fp,"c\n");
        fprintf(fp,"p cnf ");
        fprintf(fp,"%d %d\n",n_vars,n_clauses1);
        for(int i=0;i<know_num;i++){
            fscanf(fpuzzle,"%d",know_var+i);
            fprintf(fp,"%d %d\n",know_var[i],0);
        }
        printf("the binary puzzle is following:\n");
        for(int i=1,j=0;i<=n*n;i++){
            if(j<know_num&&know_var[j]==i){
                printf("%d ",1);
                j++;
            }else if(j<know_num&&know_var[j]==-i){
                printf("%d ",0);
                j++;
            }else{
                printf("? ");
            }
            if(i%n==0){
                printf("\n");
            }
        }
        fclose(fpuzzle);
        //约束1
    for(int i=1;i<=n;i++){
        for(int k=1;k<=n-2;k++){
                fprintf(fp,"%d %d %d %d\n",a[i][k],a[i][k+1],a[i][k+2],0);
                fprintf(fp,"%d %d %d %d\n",-a[i][k],-a[i][k+1],-a[i][k+2],0);
        }
    }
    for(int j=1;j<=n;j++){
        for(int k=1;k<=n-2;k++){
                fprintf(fp,"%d %d %d %d\n",a[k][j],a[k+1][j],a[k+2][j],0);
                fprintf(fp,"%d %d %d %d\n",-a[k][j],-a[k+1][j],-a[k+2][j],0);
        }
    }
    //约束2
    for(int j=1;j<=n;j++){
        C1(2*M,M+1,j);
        C2(2*M,M+1,j);
        C3(2*M,M+1,j);
        C4(2*M,M+1,j);
    }
    // 约束3
    count=2*n*n-n+1;
    recount=1;
    for(int k=1;k<=4*M*M-2*M;k++){
        remain[k]=4*M*M+k;
    }
    //行
    for(int i=1;i<=2*M-1;i++){
        for(int j=i+1;j<=2*M;j++){
            for(int k=1;k<=2*M;k++){
                zhen[k]=count++;
                fu[k]=count++;
                zong[k]=count++;
                fprintf(fp,"%d %d %d %d\n",-a[i][k],-a[j][k],zhen[k],0);
                fprintf(fp,"%d %d %d\n",a[i][k],-zhen[k],0);
                fprintf(fp,"%d %d %d\n",a[j][k],-zhen[k],0);
                fprintf(fp,"%d %d %d %d\n",a[i][k],a[j][k],fu[k],0);
                fprintf(fp,"%d %d %d\n",-a[i][k],-fu[k],0);
                fprintf(fp,"%d %d %d\n",-a[j][k],-fu[k],0);
                fprintf(fp,"%d %d %d %d\n",zhen[k],fu[k],-zong[k],0);
                fprintf(fp,"%d %d %d\n",-zhen[k],zong[k],0);
                fprintf(fp,"%d %d %d\n",-fu[k],zong[k],0);
            }
            for(int d=1;d<=2*M;d++){
                fprintf(fp,"%d %d %d\n",remain[recount],zong[d],0);
            }
            for(int d=1;d<=2*M;d++){
                fprintf(fp,"%d ",-zong[d]);
            }
            fprintf(fp,"%d %d\n",-remain[recount],0);
            recount++;
        }
    }
    //列
    for(int i=1;i<=2*M-1;i++){
        for(int j=i+1;j<=2*M;j++){
            for(int k=1;k<=2*M;k++){
                zhen[k]=count++;
                fu[k]=count++;
                zong[k]=count++;
                fprintf(fp,"%d %d %d %d\n",-a[k][i],-a[k][j],zhen[k],0);
                fprintf(fp,"%d %d %d\n",a[k][i],-zhen[k],0);
                fprintf(fp,"%d %d %d\n",a[k][j],-zhen[k],0);
                fprintf(fp,"%d %d %d %d\n",a[k][i],a[k][j],fu[k],0);
                fprintf(fp,"%d %d %d\n",-a[k][i],-fu[k],0);
                fprintf(fp,"%d %d %d\n",-a[k][j],-fu[k],0);
                fprintf(fp,"%d %d %d %d\n",zhen[k],fu[k],-zong[k],0);
                fprintf(fp,"%d %d %d\n",-zhen[k],zong[k],0);
                fprintf(fp,"%d %d %d\n",-fu[k],zong[k],0);
            }
            for(int d=1;d<=2*M;d++){
                fprintf(fp,"%d %d %d\n",remain[recount],zong[d],0);
            }
            for(int d=1;d<=2*M;d++){
                fprintf(fp,"%d ",-zong[d]);
            }
            fprintf(fp,"%d %d\n",-remain[recount],0);
            recount++;
        }
    }
    //
    fclose(fp);
    printf("success to output puzzle .cnf file at %s\n",puzzleaddr);
    //进入SAT求解阶段
    Fp=fopen(puzzleaddr,"r");
    if(!Fp){
        printf("fail to open the puzzle .cnf file\n");
        continue;
    }
    cc='a';
    do{//省略以c开头的备注
        fgets(str,MAX_LEN,Fp);
        cc=str[0];
    }while(cc=='c');
    num_var=0,num_cla=0;//分别为变量和子句数以及数值存储
    flag1=0;
    for(int i=0,j=0;;i++){ //记录VARS和CLAUSES的位数以及数值
        if(str[i]>='a'&&str[i]<='z') continue;
        if(str[i]>='0'&&str[i]<='9'){
            num[j++]=str[i]-'0';
            if(flag1==2) num_var++;
            else num_cla++;
        }else if(str[i]==' '){
            flag1++;
        }else{
            break;
        }
    }
    for(int i=0;i<num_var;i++){
        VARS=10*VARS+num[i];
    }
    for(int i=num_var;i<num_var+num_cla;i++){
        CLAUSES=10*CLAUSES+num[i];
    }
    n_clauses=r_clauses=CLAUSES;
    literal=0,literalth=0,clauseth=0;
    while(fscanf(Fp,"%d",&literal)!=EOF){ //子句和文字结构信息的存储
        if(literal!=0){
            literalth++;
            j=(literal>0)?0:1;
            i=abs(literal);
            linfo[i][j].n_occur++;
            linfo[i][j].lit_in_clauses[linfo[i][j].n_occur-1]=clauseth;
            linfo[i][j].lit_in_clauses_locs[linfo[i][j].n_occur-1]=literalth-1;
            clauses[clauseth].literals[literalth-1]=literal;
            clauses[clauseth].current_length++;
            clauses[clauseth].original_length=clauses[clauseth].current_length;
            clauses[clauseth].binary_code=2*clauses[clauseth].binary_code+1;
        }
        else{
            if(literalth==1){
                literal=gucl_stack[n_gucl++]=clauses[clauseth].current_ucl=clauses[clauseth].literals[0];
                j=(literal>0)?0:1;
                i=abs(literal);
                linfo[i][j].is_unit=YES;
                linfo[i][j].antecedent_clause=clauseth;
                clauses[clauseth].current_ucl=literal;
            }
            clauseth++;
            literalth=0;
        }
    }
    fclose(Fp);
    start=clock();
    ans = dpll();
    finish=clock();
    duration = (double)(finish - start) / CLOCKS_PER_SEC;
    duration = 1000*duration;  //化为ms
    printf("the time is %f millisecond\n",duration);
    if(!ans){
        printf("puzzle with no solution\n");
        continue;
    }
    flag1=0;
    for(int k=0;k<CLAUSES;k++){
        flag1=0;
        for(int i=0;i<clauses[k].original_length;i++){ //再检验1
            lit=clauses[k].literals[i];
            if(lit>0){
                if(assign[lit].type==TRUE){
                    flag1=1;
                    break;
                }
                else{
                    continue;
                }
            }else{
                if(assign[abs(lit)].type==FALSE){
                    flag1=1;
                    break;
                }else{
                    continue;
                }
            }
        }
        if(!flag1){
            printf("puzzle with no solution\n");
            break;
        }
    }
    if(!flag1){
        continue;
    }
    for(int i=n*n+1;i<=2*n*n-n;i++){ //再检验2
        if(!assign[i].type){
            printf("puzzle with no solution\n");
            flag1=0;
            break;
        }
    }
    if(!flag1){
        continue;
    }
        printf("get solution\n");
        memset(writeaddr,0,sizeof(writeaddr));
        strcpy(writeaddr,puzzleaddr);
        int legth=strlen(puzzleaddr);
        writeaddr[legth-3]='r';
        writeaddr[legth-2]='e';
        writeaddr[legth-1]='s';
        FILE* fpwrite;
        fpwrite=fopen(writeaddr,"wb");
        if(!fpwrite){
            printf("fail to write .res file!\n");
            continue;
        }
        fprintf(fpwrite,"s //正数表TRUE，负数表FALSE，*表未定\n");
        fprintf(fpwrite,"v\n");
        for(int i=1,type=2;i<=n*n;i++){
            type=assign[i].type;
            if(type==TRUE){
                fprintf(fpwrite,"%d ",i);
            }else if(type==FALSE){
                fprintf(fpwrite,"%d ",-i);
            }else{
                fprintf(fpwrite,"*%d",i);
            }
        }
        fprintf(fpwrite,"\nt %f",duration);
        fclose(fpwrite);
        printf("the following is the solution:\n");
        for(int i=1;i<=n;i++){
            for(int j=1;j<=n;j++){
                printf("%d  ",assign[a[i][j]].type>0?1:0);
            }
            printf("\n");
        }
    }
  else{
      break;
  }
}
    return 0;
}
