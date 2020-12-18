theory fm01_proof
imports Main
begin

section\<open>basic proof\<close>
theorem prop1: "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> C)"
  apply(rule impI) thm impI
  apply(rule impI)
  apply(rule impI)
  apply(subgoal_tac "B \<longrightarrow> C") 
   prefer 2 apply(rotate_tac) apply(erule mp) thm mp apply assumption
  apply(erule mp) apply(erule mp) apply assumption
  done

(* by blast *)
  
theorem Peirce: "((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
  apply(subst imp_conv_disj) thm imp_conv_disj thm subst
  apply(subst imp_conv_disj)
  apply(subst de_Morgan_disj) thm de_Morgan_disj
  apply(subst not_not) thm not_not
  apply(rule impI)
  apply(erule disjE) thm disjE
   apply(erule conjE) thm conjE
   apply assumption
  apply assumption
  done
(*  by blast *)

lemma assumes p: P and q: Q shows "P \<and> (Q \<and> P)"
proof (rule conjI)
  from p show P by this
next
  show "Q \<and> P"
    proof (rule conjI)
      from q show Q .
    next
      from p show P .
    qed
  qed

lemma assumes ab: "A \<or> B" and ac: "A \<longrightarrow> C" and bc: "B \<longrightarrow> C"
shows C
proof -
  note ab
  moreover {
    assume a: A
    from ac a have C by (rule mp) 
  } 
  moreover {
    assume b: B
    from bc b have C by (rule mp) 
  }
  ultimately show C by (rule disjE)
qed


section\<open>ISABELLE’S FUNCTIONAL LANGUAGE\<close>

subsection\<open>Natural numbers, integers, and booleans\<close>

(* datatype nat = Suc nat | Zero *)

lemma "Suc 0 = 1" by simp

value "Suc 0"

lemma "2 * 3 = (6::nat)" by simp

lemma "1 + -2 = (-1::int)" by simp

lemma "True \<or> False = True" by simp
lemma "\<forall>x. x = x" by simp
lemma "\<exists>x. x = 1" by simp

subsection\<open>non-recursive definition\<close>

definition XOR :: "bool \<Rightarrow> bool \<Rightarrow> bool"
  where "XOR a b \<equiv> (a \<and> \<not>b) \<or> (\<not>a \<and> b)"

value "XOR True False"
lemma "XOR True True = False"
  by(simp add:XOR_def)

subsection\<open>high-order function\<close>

definition highorder_f1 :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "highorder_f1 f x y \<equiv> f x y"

value "highorder_f1 plus 2 100"
value "highorder_f1 minus 2 100"
value "highorder_f1 times 2 100"


subsection\<open>lambda expression\<close>

value "(\<lambda>x y. (x::nat) + y) 9 8"


subsection\<open>Let expression\<close>

value "(let x = (3::nat); y = 8 in x * y)"

lemma "(let x = 3 in x * x) = (9::nat)"
  by simp

subsection\<open>pair\<close>
definition add_pair :: "(nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> (nat \<times> nat)"
  where "add_pair a b \<equiv> (fst a + fst b, snd a + snd b)"

value "add_pair (5,6) (10,12)"

subsection\<open>list\<close>

term "[1::nat,2,3,4,5]"

definition list_add :: "nat list \<Rightarrow> nat \<Rightarrow> nat list"
  where "list_add l n \<equiv> map (\<lambda>x. x + n) l"

value "list_add [1,2,3,4,5] 10"

term foldl

definition list_mul :: "nat list \<Rightarrow> nat"
  where "list_mul l \<equiv> foldl (\<lambda>x y. x * y) 1 l"

value "list_mul [1,2,3,4,5]"

subsection\<open>record\<close>

record xypt = 
  xx :: nat 
  yy :: bool

value "\<lparr>xx = 9, yy = True\<rparr>"

subsection\<open>Datatypes and primitive recursion\<close>
datatype 'a tree = Leaf | Branch "'a tree" 'a "'a tree"

(* traverse in inorder *)
primrec inorder :: "'a tree \<Rightarrow> 'a list" where
"inorder Leaf = []" |
"inorder (Branch left x right) = inorder left @ (x # inorder right)"

primrec mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Leaf = Leaf" |
"mirror (Branch left x right) = Branch (mirror right) x (mirror left)"

lemma mirror_correct: "inorder (mirror tree) = rev (inorder tree)"
  by (induct tree; simp)

lemma "inorder (mirror tree) = rev (inorder tree)"
proof(induct tree)
  case Leaf
  then show ?case by auto
next
  case (Branch tree1 x2 tree2)
  then show ?case by simp
qed

section\<open>stack\<close>

type_synonym 'a stack = "'a list"

definition push :: "'a \<Rightarrow> 'a stack \<Rightarrow> 'a stack" 
where "push v s = v#s"

primrec pop :: "'a stack \<Rightarrow> ('a \<times> 'a stack)" 
where "pop (x # xs) = (x, xs)"

(*definition empty :: "'a stack \<Rightarrow> 'a stack"
  where "empty s = []"*)

definition top :: "'a stack \<Rightarrow> 'a"
  where "top s \<equiv> hd s"

definition "emp s \<equiv> s = []"

lemma "top (push v s) = v" 
  apply(induct s) 
  by(simp add:top_def push_def)+

lemma "pop (push v s) = (v, s)"
  by (simp add:push_def)
  
lemma "\<forall>v s. pop (push v s) = (v, s)"
  by (simp add:push_def)

lemma "\<not> emp s \<Longrightarrow> top s = fst (pop s)"
  apply(induct s)
  by(simp add: emp_def top_def)+

lemma "\<not> emp s \<Longrightarrow> (v, s0) = pop s \<Longrightarrow> push v s0 = s"
  apply(simp add: emp_def push_def) 
  apply(induct s) by auto

section\<open>induction proof\<close>
(* declare [[show_types]] *)
theorem "(\<Sum>x | x < n. (2 :: nat) ^ x) = 2 ^ n - 1"
  apply(induct n) apply simp 
  apply(subgoal_tac \<open>{x. x < Suc n} = {n} \<union> {x. x < n}\<close>)
  by auto

thm sym
thm add.commute

theorem "(\<Sum>x | x < n. (2 :: nat) ^ x) = 2 ^ n - 1"
proof(induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  assume A: "(\<Sum>x | x < n. (2 :: nat) ^ x) = 2 ^ n - 1"
  have "{x. x < Suc n} = {x. x < n} \<union> {n}" by fastforce
  with A show ?case by simp
qed

section\<open>big example: a small compiler\<close>

type_synonym 'v binop = "'v \<Rightarrow> 'v \<Rightarrow> 'v"

datatype 'v expr = Const 'v | Var nat | App "'v binop" "'v expr" "'v expr"

primrec eval :: "'v expr \<Rightarrow> (nat \<Rightarrow> 'v) \<Rightarrow> 'v"
  where "eval (Const b) env = b" |
        "eval (Var x) env = env x" |
        "eval (App f e1 e2) env = (f (eval e1 env) (eval e2 env))"

datatype 'v instr = IConst 'v | ILoad nat | IApp "'v binop"

primrec exec :: "'v instr list \<Rightarrow> (nat \<Rightarrow> 'v) \<Rightarrow> 'v list \<Rightarrow> 'v list" where 
  "exec [] env vs = vs" |
  "exec (i#is) env vs = 
    (case i of IConst v \<Rightarrow> exec is env (v#vs) | 
               ILoad x \<Rightarrow> exec is env ((env x)#vs) | 
               IApp f \<Rightarrow> exec is env ((f (hd vs) (hd (tl vs)))#(tl(tl vs))))"

primrec compile :: "'v expr \<Rightarrow> 'v instr list" where
  "compile (Const v) = [IConst v]" |
  "compile (Var x) = [ILoad x]" |
  "compile (App f e1 e2) = (compile e2) @ (compile e1) @ [IApp f]"


lemma exec_append[rule_format]:
"\<forall>vs. exec (xs@ys) env vs = exec ys env (exec xs env vs)"
  apply (induct xs) 
    apply simp 
  apply auto apply (case_tac a) apply auto done


theorem "\<forall>vs. exec (compile e) env vs = (eval e env)#vs"
proof (induct e)
  fix v
  show "\<forall> vs. exec (compile (Const v)) env vs = (eval (Const v) env)#vs" by simp
next
  fix x
  show "\<forall>vs. exec (compile (Var x)) env vs = eval (Var x) env # vs" by simp
next
  fix f e1 e2
  assume IH1: "\<forall>vs. exec (compile e1) env vs = eval e1 env # vs"
     and IH2: "\<forall>vs. exec (compile e2) env vs = eval e2 env # vs"
  show "\<forall>vs. exec (compile (App f e1 e2)) env vs = eval (App f e1 e2) env # vs"
    proof
      fix vs
      have "exec (compile (App f e1 e2)) env vs = exec ((compile e2) @ (compile e1) @ [IApp f]) env vs" 
        by simp
      also have "... = exec ((compile e1) @ [IApp f]) env (exec (compile e2) env vs)"
        using exec_append by blast
      also have "... = exec [IApp f] env (exec (compile e1) env (exec (compile e2) env vs))"
        using exec_append by blast
      also have "... = exec [IApp f] env (exec (compile e1) env (eval e2 env # vs))"
        using IH2 by simp
      also have "... = exec [IApp f] env ((eval e1 env) # (eval e2 env # vs))"
        using IH1 by simp
      also have "... = (f (eval e1 env) (eval e2 env))#vs" by simp
      also have "... = eval (App f e1 e2) env # vs" by simp
      finally show "exec (compile (App f e1 e2)) env vs = eval (App f e1 e2) env # vs"
        by blast
    qed
qed


end
