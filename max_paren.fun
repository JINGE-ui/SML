fun myzip (a:int list,n:int) =
    if(n<0) then [] 
    else List.drop(a,n)::myzip(a,n-1); (*为并行依次判断作准备，调用为myzip(a,length(a)-1)*)

fun paren (a) = 
let
fun iterate([],sum,m1,m2) = m2
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