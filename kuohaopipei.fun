fun iterate([],sum):int = sum
|iterate(x::xs,sum) = 
let
fun count(s:int,1):int = s-1
    |count(s,0) = s+1
	|count(~1,_) = ~1
in
iterate(xs,count(sum,x))
end;

fun matchparens(List:int list):int=
let
val x = iterate(List,0)
in 
if(x=0) then 1
else 0
end;
val N = getInt();
val List = getIntTable(N);
printInt(matchparens(List));