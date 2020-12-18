theory Concrete_semantic
imports Main
begin
(*2.2.1 P7*)
datatype bool=True|False
fun conj::"bool\<Rightarrow>bool\<Rightarrow>bool"
  where
"conj True True=True"|
"conj _ _=False"

(*------------------*)
(*2.2.2 P8*)
fun add::"nat\<Rightarrow>nat\<Rightarrow>nat"
where
"add 0 n =n"|
"add(Suc m) n=Suc(add m n)"
lemma add_02:"add m 0=m"
apply(induction m)
apply(auto)
  done
(*------------------*)


(*2.2.3 P10,11*)
datatype 'a list = Nil | Cons 'a "'a list"

fun app::"'a list\<Rightarrow>'a list \<Rightarrow>'a list"
where
"app Nil ys = ys" |
"app(Cons x xs) ys=Cons x(app xs ys)"

fun rev::" 'a list\<Rightarrow>'a list"
where
"rev Nil = Nil " |
"rev(Cons x xs)=app(rev xs)(Cons x Nil)"
value "rev(Cons True (Cons False Nil))"
value "rev(Cons a (Cons b Nil))"
lemma app_Nil2 [simp]:"app xs Nil = xs" 
  apply(induction xs) 
  apply(auto) 
  done
lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)" 
  apply(induction xs) 
  apply(auto) 
  done
lemma rev_app [simp]:"rev(app xs ys) = app(rev ys)(rev xs)"
apply (induction xs)
   apply(auto)
  done
lemma rev_rev [simp]: "rev (rev xs) =xs"
  apply (induction xs)
   apply(auto)
  done
(*-------------------*)

(*2.2.5 P14*)
fun map::"('a\<Rightarrow>'b) \<Rightarrow> 'a list \<Rightarrow>'b list"
  where
"map f Nil=Nil"|
"map f (Cons x xs) = Cons (f x) (map f xs)"
(*-------------------*)

(*Exercises P15*)

(*2.1*)
value"1+(2::nat)"
value"1+(2::int)"
value"1-(2::nat)"
value"1-(2::int)"
(*--------------*)

(*exercise2.2*)
fun double::"nat \<Rightarrow>nat" where
"double 0=add 0 0"|
"double n=add(add n 0) n"
lemma add_com: "add m n=add n m"
apply(induction m)
   apply(auto)
fun add_1::"nat\<Rightarrow>nat"where
"add_1 add (add 0 n)p=add 0(add n p)"|
"add_1 add (add (Suc m)n) p=add (Sucm) (add n p)"
lemma add_assoc: "add (add m n)p=add m (add n p)"
apply(induction m)
   apply(auto)
  done
lemma double_add:"double m=add m m"
  apply(induction m)
   apply(auto)
  done
(*-------------------*)
(*exercise2.3*)
fun count::"'a \<Rightarrow>'a list\<Rightarrow>nat"where
"count x 0=0"|
"count x x=xs"|
"count "
(*-------------------*)

(*2.3.1 P16*)
(*e1*)
datatype 'a tree=Tip | Node "'a tree" 'a "'a tree"
fun mirror::"'a tree\<Rightarrow>'a tree"
  where
"mirror Tip=Tip"|
"mirror(Node l a r) = Node (mirror r) a (mirror l)"
lemma "mirror(mirror t) =t"
  apply(induction t)
   apply(auto)
  done
(*e2*)
datatype 'a option=None | Some 'a
fun lookup::"('a *'b)list \<Rightarrow> 'a \<Rightarrow> 'b option"
  where
"lookup [] x= None"|
"lookup ((a,b)#ps)x= (if a=x then Some b else lookup ps x)"


(*-------------------*)

(*2.3.2 P17*)
definition sq::"nat\<Rightarrow>nat"where
"sq n=n*n"
(*-------------------*)

(*2.3.3 P17*)
abbreviation sq' :: "nat\<Rightarrow>nat" where(*? ? ?*)
"sq' n=n*n"
(*------------------*)


(*2.3.4*)
fun div2::"nat\<Rightarrow>nat"where
"div2 0= 0"|
"div2 (Suc 0) = 0"|
"div2 (Suc (Suc n)) =Suc(div2 n)"
lemma "div2(n) = n div 2"
  apply(induction n rule:div2.induct)
  apply(auto)
  done
(*-------------------*)

(*2.4 P20*)
fun itrev::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
"itrev []      ys = ys" |
"itrev (x#xs) ys = itrev xs (x#ys)"
lemma "itrev xs [] = rev xs"
  apply(induction xs)
  apply(auto)
lemma "itrev xs ys=rev xs @ ys"
  apply(induction xs arbitrary: ys)
  apply(auto)
  done
(*---------------*)

(*3.12 P29*)
type_synonym vname=string
datatype aexp=N int | V vname | Plud aexp aexp
type_synonym val=int
type_synonym state = vname\<Rightarrow>val(*? ? ?*)
fun aval::"aexp \<Rightarrow> state \<Rightarrow> val"
  where
"aval (N n) s =n"|
"aval (V x) s=s x"|
"aval (Plus a b)s=aval a s +aval b s"

value "aval (Plus (N 3)(V ''x'')) (\<lambda>x.0)"