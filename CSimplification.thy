theory CSimplification
imports Main
begin

lemma "\<lbrakk> xs @ zs = ys @ xs; [] @ xs = [] @ [] \<rbrakk> \<Longrightarrow> ys = zs"
apply simp (* Applies x = [] *)
done

lemma "\<forall>x. f x = g (f (g x)) \<Longrightarrow> f [] = f [] @ []"
apply (simp (no_asm)) (* No assumptions \<rightarrow> prevent nontermination *)
done

definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"xor A B \<equiv> (A \<and> \<not>B) \<or> (\<not>A \<and> B)"

lemma "xor A (\<not>A)"
(*
apply (simp only: xor_def)
apply (simp only: or_def)
apply (simp only: not_def)
apply (simp only: and_def)
... ?
*)
(*
apply (simp only: xor_def) (* unfold xor *)
apply simp
*)
apply (simp add: xor_def)
done

(* Apply simplification plus Let_def *)
lemma "(let xs = [] in xs @ ys @ xs) = ys"
apply (simp add: Let_def)
done

(* Add Let_def to simplification and apply simplification *)
declare Lef_def [simp]
lemma "(let xs = [] in xs @ ys @ xs) = ys"
apply simp
done

(* Remove Let_def from simplification *)
(* Why doesn't this work? *)
(*
declare Let_def [simp del]
\<Longrightarrow>
Rewrite rule not in simpset:
Let ?s ?f \<equiv> ?f ?s
*)

(* Conditional equations *)
lemma hd_Cons_tl [simp]: "xs \<noteq> [] \<Longrightarrow> hd xs # tl xs = xs"
apply (case_tac xs, simp, simp)
done (* Duplicate rule of List.hd_Cons_tl *)

lemma "xs \<noteq> [] \<Longrightarrow> hd (rev xs) # tl (rev xs) = rev xs"
apply simp
done

(* Automatic case split *)
lemma "\<forall>xs. if xs = [] then rev xs = [] else rev xs \<noteq> []"
(* Split with the theorem to split ifs. *)
apply (split split_if) (* Not strictly necessary because it's already done by simp. *)
apply simp
done

lemma "(case xs of [] \<Rightarrow> zs | y # ys \<Rightarrow> y # ys @ zs) = xs @ zs"
(* Split with theorem to split lists. *)
(*
apply (split list.split)
apply simp
*)
apply (simp split: list.split) (* Combined above *)
done

lemma "(if xs = [] then ys \<noteq> [] else ys = []) \<Longrightarrow> xs @ ys \<noteq> []"
(* Apply split_if to the assumptions only *)
apply (split split_if_asm)
(*
apply simp
apply simp
*)
apply simp_all
done

end
