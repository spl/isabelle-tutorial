(* Section 3.3 *)

theory ECompiling
imports Main
begin

(* Binary operation *)
type_synonym 'v binop = "'v \<Rightarrow> 'v \<Rightarrow> 'v"

(* Expression language *)
datatype ('a, 'v) expr = Cex 'v (* Constants *)
                       | Vex 'a (* Variables *)
                       | Bex "'v binop" "('a, 'v) expr" "('a, 'v) expr" (* Application *)

(* Value of expression wrt environment *)
primrec "value" :: "('a, 'v) expr \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'v" where
"value (Cex c) env = c" |
"value (Vex v) env = env v" |
"value (Bex f e1 e2) env = f (value e1 env) (value e2 env)"

(* Stack machine instructions *)
datatype ('a, 'v) instr = Const 'v
                        | Load 'a
                        | Apply "'v binop"

(* Execution of stack machine instructions *)
primrec exec :: "('a, 'v) instr list \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'v list \<Rightarrow> 'v list" where
"exec [] s vs = vs" |
"exec (i # is) s vs = (case i of
    Const c \<Rightarrow> exec is s (c # vs)
  | Load a \<Rightarrow> exec is s (s a # vs)
  | Apply f \<Rightarrow> exec is s (f (hd vs) (hd (tl vs)) # tl (tl vs)))"

(* Compile an expression into a list of instructions *)
primrec compile :: "('a, 'v) expr \<Rightarrow> ('a, 'v) instr list" where
"compile (Cex c) = [Const c]" |
"compile (Vex v) = [Load v]" |
"compile (Bex f e1 e2) = compile e2 @ compile e1 @ [Apply f]"

(*
Goal:
theorem "exec (compile e) s [] = [value e s]"
*)

(* First prove execution with concatenated lists *)
lemma exec_app[simp]: "\<forall>vs. exec (xs @ ys) s vs = exec ys s (exec xs s vs)"
apply (induct_tac xs)
apply simp
apply (simp split: instr.split)
done

(* Generalized goal: executing a compiled program results in the value of the program *)
theorem "\<forall>vs. exec (compile e) s vs = value e s # vs"
apply (induct_tac e)
apply simp_all
done
