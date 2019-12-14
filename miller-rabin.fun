fun isprime(n:IntInf.int,a:IntInf.int) = 
if n = 2 then 1 else 
if n = 1 orelse n mod 2 = 0 then 0 else 
let
    val d = get(n-1);
    val t = pow(a,d,n);
    fun def(d,t) = 
    if d = n - 1 orelse t = 1 orelse t = n - 1 then if t = n - 1 orelse d mod 2 = 1 then 1 else 0 
    else def(d * 2,(t*t) mod n)
in def(d,t)
end;

fun pow (a:IntInf.int,n:IntInf.int,m:IntInf.int):IntInf.int = 
let 
	val x = 1;
	val p = a mod m;
    fun qui(n,x,p)=
	    if n = 0 then x
		else if n mod 2 = 1 then qui(n div 2,(x*p) mod m,(p*p) mod m)
		else qui(n div 2,x,(p*p) mod m)
in qui(n,x,p) end;

fun get(d:IntInf.int) =
if(d mod 2 = 1) then d
else get(d div 2); 



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
