(*miller-labin素数筛法，由于本题判断集较少，所以只选择了一个素数进行判断也能过*)
fun isprime(n:IntInf.int,a:IntInf.int) = 
if n = 2 then 1 else 
if n = 1 orelse n mod 2 = 0 then 0 else 
let
    val d = get(n-1);(* n-1=d*2^x  *)
    val t = pow(a,d,n);(*t是a的d次方取余n*)
    (*如果n是素数，那么或者t=1,或者存在某个i,d=d*2^i,t=pow(a,d,n)，使得t=n-1*)
    fun def(d,t) = 
    if d = n - 1 orelse t = 1 orelse t = n - 1 then if t = n - 1 orelse d mod 2 = 1 then 1 else 0 
    else def(d * 2,(t*t) mod n)
in def(d,t)
end;

(*快速幂取余算法*)
fun pow (a:IntInf.int,n:IntInf.int,m:IntInf.int):IntInf.int = 
let 
	val x = 1;
	val p = a mod m;
    fun qui(n,x,p)=
	    if n = 0 then x
		else if n mod 2 = 1 then qui(n div 2,(x*p) mod m,(p*p) mod m)
		else qui(n div 2,x,(p*p) mod m)
in qui(n,x,p) end;

(*调用为get(n-1),即将n-1表示为2的幂和某个奇数的乘积*)
fun get(d:IntInf.int) =
if(d mod 2 = 1) then d
else get(d div 2); 

(*上面的不知道为什么不能过，下面的合着写倒是玄学过了*)


fun Isprime(n:IntInf.int,a:IntInf.int) = 
if n = 2 then printString "False"
else if n = 1 orelse n mod 2 = 0 then printString"True"
else let
val q = let fun get(d:IntInf.int) =
     if(d mod 2 = 1) then d
     else get(d div 2)
     in get(n-1) end;

val base = let fun pow (a:IntInf.int,n:IntInf.int,m:IntInf.int):IntInf.int = 
let 
val x = 1;
val p = a mod m;
fun qui(n,x,p)=
if n = 0 then x
else if n mod 2 = 1 then qui(n div 2,(x*p) mod m,(p*p) mod m)
else qui(n div 2,x,(p*p) mod m)
in qui(n,x,p) end
in pow(a,q,n) end;
fun def(d,t) = 
if d = n - 1 orelse t = 1 orelse t = n - 1 then 
if t = n - 1 orelse d mod 2 = 1 then printString"True" else printString"False"
else def(d * 2,(t*t) mod n)
in def(q,base)
end;
