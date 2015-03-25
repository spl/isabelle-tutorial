(* Section 2.5 *)
theory BDatatypes
imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

primrec mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node t\<^sub>1 x t\<^sub>2) = Node (mirror t\<^sub>2) x (mirror t\<^sub>1)"

lemma mirror_mirror: "mirror (mirror t) = t"
apply (induct_tac t)
apply auto
done

primrec flatten :: "'a tree \<Rightarrow> 'a list" where
"flatten Tip = []" |
"flatten (Node t\<^sub>1 x t\<^sub>2) = flatten t\<^sub>1 @ [x] @ flatten t\<^sub>2"

lemma "flatten (mirror t) = rev (flatten t)"
apply (induct_tac t)
apply auto
done

lemma "(case xs of [] \<Rightarrow> [] | y # ys \<Rightarrow> xs) = xs"
apply (case_tac xs)
apply auto
done

datatype boolex = Const bool | Var nat | Neg boolex | And boolex boolex

primrec "value" :: "boolex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" where
"value (Const b) env = b" |
"value (Var n)   env = env n" |
"value (Neg b)   env = (\<not> value b env)" |
"value (And b c) env = (value b env \<and> value c env)"

datatype ifex = CIF bool | VIF nat | IF ifex ifex ifex

primrec valif :: "ifex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" where
"valif (CIF b)    env = b" |
"valif (VIF n)    env = env n" |
"valif (IF c t f) env = (if valif c env then valif t env else valif f env)"

primrec bool2if :: "boolex \<Rightarrow> ifex" where
"bool2if (Const b) = CIF b" |
"bool2if (Var n)   = VIF n" |
"bool2if (Neg b)   = IF (bool2if b) (CIF False) (CIF True)" |
"bool2if (And b c) = IF (bool2if b) (bool2if c) (CIF False)"

lemma "valif (bool2if b) env = value b env"
apply (induct_tac b)
apply auto
done

primrec normif :: "ifex \<Rightarrow> ifex \<Rightarrow> ifex \<Rightarrow> ifex" where
"normif (CIF b) t f      = IF (CIF b) t f" |
"normif (VIF n) t f      = IF (VIF n) t f" |
"normif (IF c c\<^sub>1 c\<^sub>2) t f = normif c (normif c\<^sub>1 t f) (normif c\<^sub>2 t f)"

primrec norm :: "ifex \<Rightarrow> ifex" where
"norm (CIF b) = CIF b" |
"norm (VIF n) = VIF n" |
"norm (IF c t f) = normif c (norm t) (norm f)"

lemma [simp]: "\<forall>t e. valif (normif b t e) env = valif (IF b t e) env"
apply (induct_tac b)
apply auto
done

theorem "valif (norm b) env = valif b env"
apply (induct_tac b)
apply auto
done

primrec normal :: "ifex \<Rightarrow> bool" where
"normal (CIF b)    = True" |
"normal (VIF n)    = True" |
"normal (IF c t f) = ((case c of CIF b \<Rightarrow> True | VIF n \<Rightarrow> True | IF x y z \<Rightarrow> False)
                   \<and> normal t
                   \<and> normal f)"

lemma [simp]: "\<forall>t f. normal (normif c t f) = (normal t \<and> normal f)"
apply (induct_tac c)
apply auto
done

theorem "normal (norm b)"
apply (induct_tac b)
apply auto
done

(* Strengthened s.t. the first argument to IF must be a variable *)
primrec normif' :: "ifex \<Rightarrow> ifex \<Rightarrow> ifex \<Rightarrow> ifex" where
"normif' (CIF b) t f      = (if b then t else f)" |
"normif' (VIF n) t f      = IF (VIF n) t f" |
"normif' (IF c c\<^sub>1 c\<^sub>2) t f = normif' c (normif' c\<^sub>1 t f) (normif' c\<^sub>2 t f)"

primrec norm' :: "ifex \<Rightarrow> ifex" where
"norm' (CIF b) = CIF b" |
"norm' (VIF n) = VIF n" |
"norm' (IF c t f) = normif' c (norm' t) (norm' f)"

lemma [simp]: "\<forall>t e. valif (normif' b t e) env = valif (IF b t e) env"
apply (induct_tac b)
apply auto
done

theorem "valif (norm' b) env = valif b env"
apply (induct_tac b)
apply auto
done

primrec normal' :: "ifex \<Rightarrow> bool" where
"normal' (CIF b)    = True" |
"normal' (VIF n)    = True" |
"normal' (IF c t f) = ((case c of CIF b \<Rightarrow> False | VIF n \<Rightarrow> True | IF x y z \<Rightarrow> False)
                    \<and> normal' t
                    \<and> normal' f)"

lemma [simp]: "\<forall>t f. (normal' t \<and> normal' f) \<longrightarrow> normal' (normif' c t f)"
apply (induct_tac c)
apply auto
done

theorem "normal' (norm' b)"
apply (induct_tac b)
apply auto
done

end
