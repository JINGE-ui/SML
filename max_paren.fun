(*定义一个串是闭合的，当且仅当它由'('和')'构成，而且满足以下条件之一：
空串：这个串为空
连接：这个串由两个闭合的串连接构成
匹配：这个串是一个闭合的串外面包裹一个括号构成的
本题要求在于找出最长匹配串的长度
*)

fun myzip (a:int list,n:int) =
    if(n<0) then [] 
    else List.drop(a,n)::myzip(a,n-1); (*为并行依次判断作准备，调用为myzip(a,length(a)-1)*)
(*drop:returns what is left after dropping the first i elements of the list l.*)
(*myzip得到的是a序列后缀的从小到大的排列*)
fun paren (a) = 
let
fun iterate([],sum,m1,m2) = m2
(*m1是已经遍历，正等待匹配的括号数，m2是当前匹配合格数
由于多个匹配的括号序列接连的也是匹配的，所以当匹配完成，即sum=0时不能马上退出，而是将m1清零，m2=m2+m1+1来处理*)
|iterate(x::xs,sum,m1,m2) = 
let
fun count(s:int,1):int = s-1
    |count(s,0) = s+1
	|count(~1,_) = ~1
in 
if(count(sum,x)<0) then m2
else if(count(sum,x)=0) then iterate(xs,count(sum,x),0,m1+m2+1)
else iterate(xs,count(sum,x),m1+1,m2)
end;
in 
iterate(a,0,0,0)
end;

fun fin ([],m:int) = m
|fin(x::[],m) = m
|fin(x::y::xs,m) = if y>x andalso x>0 then fin(y::xs,Int.max(m,x+2))
else fin(y::xs,m);

val a = getIntTable(getInt());
printInt(fin(map paren(myzip(a,length(a)-1)),0));