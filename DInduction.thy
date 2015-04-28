theory DInduction
imports Main BDatatypes
begin

(* Section 3.2 *)

(* Rules of thumb (ROT) for generalizing the goal before induction *)

(* Linear-time, tail-recursive version of rev with accumulator *)
primrec itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev []       ys = ys" |
"itrev (x # xs) ys = itrev xs (x # ys)"

(*
lemma "itrev xs [] = rev xs"
apply (induct_tac xs)
apply simp_all (* Does not include the induction hypothesis *)
*)

(* ROT: Generalize goals for induction by replacing constants with variables *)


(*
lemma "itrev xs ys = rev xs @ ys"
apply (induct_tac xs)
apply simp_all (* Requires specific ys but should be for all ys *)
*)

(* We're not doing induction on ys, so they should be quantified over. *)

(* ROT: Generalize goals for induction by universally quantifying over all free
   variables, except the induction variable itself. *)

lemma "\<forall>ys. itrev xs ys = rev xs @ ys"
apply (induct_tac xs)
apply simp_all
done

(* ROT: The rhs of an equation should be (in some sense) simpler than the lhs. *)

(* What happens if the lhs is simpler that the rhs? *)
(*
lemma "\<forall>ys. rev xs @ ys = itrev xs ys"
apply (induct_tac xs)
apply simp_all
(* What to do here? *)
*)

(* Exercise 3.2.1 *)
primrec add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add m 0       = m" |
"add m (Suc n) = add (Suc m) n"

lemma "\<forall>m. add m n = m + n"
apply (induct_tac n)
apply simp_all
done

(* Exercise 3.2.2 *)
primrec flatten\<^sub>2 :: "'a tree \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"flatten\<^sub>2 Tip           ys = ys" |
"flatten\<^sub>2 (Node t\<^sub>1 x t\<^sub>2) ys = flatten\<^sub>2 t\<^sub>1 (x # flatten\<^sub>2 t\<^sub>2 ys)"

lemma "\<forall>ys. flatten\<^sub>2 t ys = flatten t @ ys"
apply (induct_tac t)
apply simp_all
done

end
