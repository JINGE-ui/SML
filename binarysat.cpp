#include<stdlib.h>
#include<stdio.h>
#include<math.h>
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
#define MAX_LEN 200
#define MAX_VARS 50
#define MAX_CLAUSES 100
//数据结构
typedef struct literal_info{ //关于文字有关信息的数据结构
    int is_assigned; //是否已被确定YES/NO
    int n_occur; //该文字所在子句的数目
    int lit_in_clauses[MAX_CLAUSES]; //包含此文字的子句链
    int lit_in_clauses_locs[MAX_CLAUSE_LEN]; //在相应子句中的该文字的位置链
    int is_unit; //文字k是子句C中唯一未确定时，取YES
    int antecedent_clause; //取C
}literal_info;
literal_info linfo[MAX_VARS][2]; //对于每一变量j的正负文字 j、-j都储存信息

typedef struct clause_info //子句
{
    int literals[MAX_VARS]; //指向子句所包含的所有文字链
    int current_length; //子句的现在长度
    int original_length; //子句的原始长度
    int is_satisfied; //子句是否满足 YES/NO
    int binary_code; //o-1串，对应于连接的文字链，未确定为1，假值取0
    int current_ucl; //如果是单子句则储存对应的文字，否则取0
}clause_info;
clause_info clauses[MAX_CLAUSES]; //子句链
int n_clauses,r_clauses; //分别为原始和现在子句长度（子句满足则移出子句链）

typedef struct changes_info //记录变化
{
    int clause_index; //每当一个子句满足，被保存
    int literal_index; //一个未确定的文字确定为F时，两者都被保存
}changes_info;
changes_info changes[MAX_CLAUSES];
unsigned int changes_index; //变化索引
unsigned int n_changes[MAX_VARS][2]; //n_changes[depth][SATISFIED]/[SHRUNK]分别表示在depth层clauses satisfied和clauses shrunk的数目

typedef struct assign_info //每个变量的赋值信息
{
    int type; //TRUE/FALSE/UNASSIGNED
    int depth; //被赋值的层数
    int decision; //ASSIGN_BRANCHED1分支选择时确定/ASSIGN_IMPLIED2被迫确定/ASSIGN_NONE0未确定
}assign_info;
assign_info assign[MAX_VARS];

int contradictory_unit_clauses,conflicting_literal; //无法满足时
int depth,backtrack_level,max_depth,n_backtracks;//depth为分支树中节点的级别,backtrack_level通常等于depth-1
int ic_cnt,impl_clauses[MAX_CLAUSES];//矛盾时储存先行子句
int n_gucl; //构造大小为n_gucl大小的栈，发现单子句时压入栈
int gucl_stack[MAX_CLAUSES];

void SetVar(int v){ //计算F|v，以v为true
    register int i;
    register int p=abs(v),q=(v>0)?SATISFIED:SHRUNK;
    for(i=0;i<linfo[p][q].n_occur;++i){ //搜索v
        register int j=linfo[p][q].lit_in_clauses[i]; //j是包含v的子句
        if(clauses[j].is_satisfied) continue;
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
            register int loc=int(log2(clauses[j].binary_code));
            register int w=clauses[j].literals[loc]; //单子句中的文字，记为w
            register int s=abs(w),t=(w>0)?SATISFIED:SHRUNK;
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
    while(n_changes[depth][SHRUNK]){ //该层所有确定了全部返回
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
    for(i=1;i<=MAX_VARS;++i){
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
    register int j,c;
    s=t=0;
    for(j=0;j<linfo[x][SATISFIED].n_occur;++j){
        c=linfo[x][SATISFIED].lit_in_clauses[j];
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
    register unsigned int i,k;
    register unsigned int max=0,r,s,t;
    register int u;
    for(i=0;i<MAX_VARS;i++){
        if(assign[i].decision==ASSIGN_NONE){
            k=get_length_of_shortest_unsatisfied_clause();
            get_MOMS(i,k,s,t);
            r=(s+1)*(t+1);
            if(r>max){
                max=r;
                if(s>=t){
                    u=i;
                }else{
                    u=-i;
                }
            }
        }
    }
    return u;
}
int dpll(){ //返回UNSET或SET
    int* lucl_stack=NULL;//大小为n_lucl的动态可分配的栈，记录已确定的子句，当dpll返回unset时释放此栈
    register unsigned int n_lucl=0;
    int*ml_stack=NULL;
    int n_ml=0;
    while(1){
        if(contradictory_unit_clauses){
            ic_cnt=0;
            int cl=abs(conflicting_literal); //cl为矛盾文字
            impl_clauses[ic_cnt++]=linfo[cl][SATISFIED].antecedent_clause; //正负文字所在的单子句都存入矛盾先行数组
            impl_clauses[ic_cnt++]=linfo[cl][SHRUNK].antecedent_clause;
            assign[cl].decision=ASSIGN_NONE;
            while(n_lucl){ //是否有单子句
                UnSetVar(lucl_stack[--n_lucl]);
                register int s=abs(lucl_stack[n_lucl]);
                register int t=lucl_stack[n_lucl]>0?TRUE:FALSE;
                impl_clauses[ic_cnt++]=linfo[s][t].antecedent_clause;
                assign[s].type=UNASSIGNED;
                assign[s].decision=ASSIGN_NONE;
            }
            contradictory_unit_clauses=FALSE;
            free(lucl_stack);
            n_gucl=0;
            return UNSAT;
        }
        else if(n_gucl){ //是否有单子句
            lucl_stack=(int*)realloc(lucl_stack,(n_lucl+1)*sizeof(int));
            register int implied_lit=gucl_stack[--n_gucl];
            lucl_stack[n_gucl++]=implied_lit;
            assign[abs(implied_lit)].type=implied_lit>0?TRUE:FALSE;
            assign[abs(implied_lit)].decision=ASSIGN_IMPLIED;
            SetVar(implied_lit); //使用该强行确定的文字implied_lit确定剩余公式
            //n_units++;
        }
        else break;
    }
    //优化算法，找出单调文字v,即只出现v没有-v
    for(int i=1;i<=MAX_VARS;++i){
        int x,y,u,C;
        x=y=0;
        if(assign[i].decision==ASSIGN_NONE){
            u=0;
            for(int j=0;j<linfo[i][SATISFIED].n_occur;++j){
                C=linfo[i][SHRUNK].lit_in_clauses[j];
                x+=1-clauses[C].is_satisfied;
            }
            for(int j=0;j<linfo[i][SHRUNK].n_occur;++j){
                C=linfo[i][SHRUNK].lit_in_clauses[j];
                y+=1-clauses[C].is_satisfied;
            }
            if(x&&!y){
                u=i;
            }
            if(y&&!x){
                u=-i;
            }
            if(u){
                ml_stack=(int*)realloc(ml_stack,(n_ml+1)*sizeof(int));
                ml_stack[n_ml++]=u;
                assign[abs(u)].type=u>0?TRUE:FALSE;
                assign[abs(u)].depth=depth;
                assign[abs(u)].decision=ASSIGN_IMPLIED;
                SetVar(u);
            }
        }
    }
    //branching
    if(!r_clauses){ //子句当前长度为0，返回
        return SAT;
    }
    for(int i=1;i<=MAX_VARS;++i){
        int x,y,u,C;
        x=y=0;
        if(assign[i].decision==ASSIGN_NONE){
            u=0;
            for(int j=0;j<linfo[i][SATISFIED].n_occur;++j){
                C=linfo[i][SHRUNK].lit_in_clauses[j];
                x+=1-clauses[C].is_satisfied;
            }
            for(int j=0;j<linfo[i][SHRUNK].n_occur;++j){
                C=linfo[i][SHRUNK].lit_in_clauses[j];
                y+=1-clauses[C].is_satisfied;
            }
            if(x&&!y){
                u=i;
            }
            if(y&&!x){
                u=-i;
            }
            if(u){
                ml_stack=(int*)realloc(ml_stack,(n_ml+1)*sizeof(int));
                ml_stack[n_ml++]=u;
                assign[abs(u)].type=u>0?TRUE:FALSE;
                assign[abs(u)].depth=depth;
                assign[abs(u)].decision=ASSIGN_IMPLIED;
                SetVar(u);
            }
        }
    }
    //
    register int v=GetLiteralMinLen(); //分支规则，选择一个v
    assign[abs(v)].type=v>0?TRUE:FALSE;
    assign[abs(v)].depth=depth;
    assign[abs(v)].decision=ASSIGN_BRANCHED;
    SetVar(v);
    if(dpll()){ //递归调用dpll
        return SAT;
    }
    UnSetVar(v);
    assign[abs(v)].decision=ASSIGN_NONE;
    register int max_depth=0,i,j,k,m,left=FALSE;
    if(ic_cnt){
        while(ic_cnt){ //由于上一分支造成的全部回溯
            i=impl_clauses[--ic_cnt];
            k=clauses[i].original_length;
            for(j=0;j<k;++j){
                m=abs(clauses[i].literals[j]);
                if(assign[m].decision=ASSIGN_BRANCHED&&assign[m].depth>max_depth){
                    max_depth=assign[m].depth;
                }
            }
        }
        left=TRUE;
    }
    //backtrackinf and backjumping
    ++n_backtracks;
    if(backtrack_level>=depth-1){
        assign[abs(v)].type=!assign[abs(v)].type;
        assign[abs(v)].decision=ASSIGN_IMPLIED; //确定类型改为强迫
        SetVar(-v); //将-v设为正确，往右子树递归
        if(dpll()){
            return SAT;
        }
        UnSetVar(-v);
        assign[abs(v)].type=UNASSIGNED;
        assign[abs(v)].decision=ASSIGN_NONE;
        if(left&&ic_cnt){
            while(ic_cnt){ //由于上一分支造成的全部回溯
                i=impl_clauses[--ic_cnt];
                k=clauses[i].original_length;
                for(j=0;j<k;j++){
                    m=abs(clauses[i].literals[j]);
                    if(assign[m].decision==ASSIGN_BRANCHED&&assign[m].depth>max_depth){
                        max_depth=assign[m].depth;
                    }
                }
            }
            if(max_depth<backtrack_level){
                backtrack_level=max_depth;
            }
        }
    }
    //由于单调文字判断不合法，回溯
    while(n_ml){
        int u=ml_stack[--n_ml];
        UnSetVar(u);
        assign[abs(u)].type=UNASSIGNED;
        assign[abs(u)].decision=ASSIGN_NONE;
    }
    //
    ic_cnt=0;
    while(n_lucl){
        int z=lucl_stack[--n_lucl];
        UnSetVar(z);
        assign[abs(z)].type=UNASSIGNED;
        assign[abs(z)].decision=ASSIGN_NONE;
    }
    free(lucl_stack);
    contradictory_unit_clauses=FALSE;
    return UNSAT;
}
void getansfile(int VARS)
{
    FILE*fpwrite=fopen("E:\\sat-20.txt","w");
    if(!fpwrite)
    {
        exit(1);
    }
    for(int i=1;i<=VARS;i++){
        printf("%d  %d\n",i,assign[i-1]);
        //fprintf(fpwrite,"  %d\n",assign[i-1]);
    }
    fclose(fpwrite);
}

//读取文件
int main()
{
    FILE* fp;
    char str[MAX_LEN],c='a';
    if((fp=fopen("E:\\sat-20.cnf","r"))==NULL){
        printf("Fail to open the .cnf file!");
        exit(0);
    }
    do{//省略以c开头的备注
        fgets(str,MAX_LEN,fp);
        c=str[0];
    }while(c=='c');
    int num_var=0,num_cla=0,num[MAX_LEN/2];//分别为变量和子句数以及数值存储
    int flag=0;//判断是否已浏览变量数
    int VARS=0,CLAUSES=0;
    for(int i=0,j=0;;i++){ //记录MAX_VARS和MAX_CLAUSES的位数以及数值
        if(str[i]>='a'&&str[i]<='z') continue;
        if(str[i]>='0'&&str[i]<='9'){
            num[j++]=str[i]-'0';
            if(flag==2) num_var++;
            else num_cla++;
        }else if(str[i]==' '){
            flag++;
        }else break;
    }
    for(int i=0;i<num_var;i++){
        VARS=10*VARS+num[i];
    }
    for(int i=num_var;i<num_var+num_cla;i++){
        CLAUSES=10*CLAUSES+num[i];
    }
    //子句和文字存储
    /*
    clauses=(clause_info*)malloc(sizeof(clause_info)*CLAUSES);
    if(clauses==NULL){
        printf("fail to malloc!");
        exit(0);
    }
    for(int i=0;i<MAX_VARS;i++){//初始化子句和文字结构中的指针链
        for(int m=0;m<2;m++){
            linfo[i][m].lit_in_clauses=(int*)malloc(sizeof(int)*CLAUSES);
            if(linfo[i][m].lit_in_clauses==NULL){
                printf("fail to malloc!");
                exit(0);
            }
            linfo[i][m].lit_in_clauses=(int*)malloc(sizeof(int)*CLAUSES);
            if(linfo[i][m].lit_in_clauses==NULL){
                printf("fail to malloc!");
                exit(0);
            }
        }
    }
    for(int i=0;i<CLAUSES;i++){
        clauses[i].literals=(int*)malloc(sizeof(int)*MAX_CLAUSE_LEN);
        if(clauses[i].literals==NULL){
            printf("fail to malloc!");
            exit(0);
        }
    }
    */
   n_clauses=r_clauses=CLAUSES;
    int literal=0,literalth=0,clauseth=0;
    int j,i;
    while(fscanf(fp,"%d",&literal)!=EOF){ //子句和文字结构信息的存储
        if(literal!=0){
            literalth++;
            j=(literal>0)?0:1;
            i=abs(literal)-1;
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
                clauses[clauseth].current_ucl=clauses[clauseth].literals[0];
            }
            clauseth++;
            literalth=0;
        }
    }
    fclose(fp);
    printf("%d\n",dpll());
    system("pause");
    //getansfile(VARS);
    return 0;
}
