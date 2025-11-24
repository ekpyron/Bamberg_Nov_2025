theory T5_Embeddings
  imports Main
begin

text\<open>An Embedding is the representation of one logical system (the target logic)
     within another (the meta logic).
     We can distinguish between deep and shallow embeddings; roughly speaking:
     \<^item> Deep Embeddings represent the target logic's syntactical element using a recursive datatype
       and specify its semantics via an evaluation function.
     \<^item> Shallow Embeddings *define* the syntactic elements of the target logic directly in the
       meta-logic using their semantics.\<close>

section\<open>Simple example: Addition\<close>

text\<open>We look at a simple language of addition. It has expressions consisting of:
      \<^item> A constant symbol for 0
      \<^item> Variable symbols x, y, z
      \<^item> Expressions, which are either 0, a variable, or the addition of two expressions.
    And formulas consisting of:
      \<^item> Equality between two expressions.
      \<^item> Less-or-equal-than relation between two expressions.
      \<^item> Negations of a formula
      \<^item> Implications of two formulas
\<close>

subsection\<open>Simple example of a Deep Embedding of a simple language with Addition\<close>

datatype vars\<^sub>d = x\<^sub>d | y\<^sub>d | z\<^sub>d
datatype expression\<^sub>d = Zero\<^sub>d ("0\<^sub>d") | Var\<^sub>d vars\<^sub>d ("V'(_')") |
                       Add\<^sub>d expression\<^sub>d expression\<^sub>d (infixl "+\<^sub>d" 200)
primrec eval :: "(vars\<^sub>d \<Rightarrow> int) \<Rightarrow> expression\<^sub>d \<Rightarrow> int" where
  "eval f 0\<^sub>d = 0"
| "eval f V(x) = f x"
| "eval f (x +\<^sub>d y) = eval f x + eval f y"

datatype formula\<^sub>d =
  Equal\<^sub>d expression\<^sub>d expression\<^sub>d (infixr "=\<^sub>d" 100)
  | Leq\<^sub>d expression\<^sub>d expression\<^sub>d (infixr "\<le>\<^sub>d" 100)
  | Not\<^sub>d formula\<^sub>d ("\<not>\<^sub>d_" [40] 40)
  | Imp\<^sub>d formula\<^sub>d formula\<^sub>d (infixr "\<rightarrow>\<^sub>d" 25)

primrec rel_truth :: "(vars\<^sub>d \<Rightarrow> int) \<Rightarrow> formula\<^sub>d \<Rightarrow> bool" where
  "rel_truth f (x =\<^sub>d y) = (eval f x = eval f y)"
| "rel_truth f (x \<le>\<^sub>d y) = (eval f x \<le> eval f y)"
| "rel_truth f (\<not>\<^sub>d\<phi>) = (\<not>rel_truth f \<phi>)"
| "rel_truth f (\<phi> \<rightarrow>\<^sub>d \<psi>) = (rel_truth f \<phi> \<longrightarrow> rel_truth f \<psi>)"

definition valid\<^sub>d :: "formula\<^sub>d \<Rightarrow> bool" ("\<Turnstile>\<^sub>d_" [10] 10) where
  "valid\<^sub>d \<phi> \<equiv> \<forall> f . rel_truth f \<phi>"

definition And\<^sub>d :: "formula\<^sub>d \<Rightarrow> formula\<^sub>d \<Rightarrow> formula\<^sub>d" (infixr "\<and>\<^sub>d" 25) where
  "\<phi> \<and>\<^sub>d \<psi> \<equiv> \<not>\<^sub>d(\<phi> \<rightarrow>\<^sub>d \<not>\<^sub>d\<psi>)"

lemma "\<Turnstile>\<^sub>d (V(x\<^sub>d) +\<^sub>d V(y\<^sub>d)) =\<^sub>d (V(y\<^sub>d) +\<^sub>d V(x\<^sub>d))"
  by (auto simp: valid\<^sub>d_def)
lemma "\<Turnstile>\<^sub>d (0\<^sub>d \<le>\<^sub>d V(x\<^sub>d)) \<rightarrow>\<^sub>d (V(y\<^sub>d) \<le>\<^sub>d V(y\<^sub>d) +\<^sub>d V(x\<^sub>d))"
  by (auto simp: valid\<^sub>d_def)
lemma "\<Turnstile>\<^sub>d (V(x\<^sub>d) \<le>\<^sub>d V(y\<^sub>d) \<and>\<^sub>d V(y\<^sub>d) \<le>\<^sub>d V(x\<^sub>d)) \<rightarrow>\<^sub>d (V(x\<^sub>d) =\<^sub>d V(y\<^sub>d))"
  by (auto simp: valid\<^sub>d_def And\<^sub>d_def)

subsection\<open>Simple example of a Shallow Embedding of a simple language with Addition\<close>

type_synonym expression\<^sub>s = int
definition Zero\<^sub>s :: "int" ("0\<^sub>s") where "Zero\<^sub>s \<equiv> 0"
definition Add\<^sub>s :: "expression\<^sub>s \<Rightarrow> expression\<^sub>s \<Rightarrow> expression\<^sub>s" (infixl "+\<^sub>s" 200) where
  "Add\<^sub>s x y \<equiv> x + y"

type_synonym formula\<^sub>s = bool

definition Equal\<^sub>s :: \<open>expression\<^sub>s \<Rightarrow> expression\<^sub>s \<Rightarrow> formula\<^sub>s\<close> (infixr "=\<^sub>s" 100) where
  "Equal\<^sub>s x y \<equiv> x = y"
definition Leq\<^sub>s :: \<open>expression\<^sub>s \<Rightarrow> expression\<^sub>s \<Rightarrow> formula\<^sub>s\<close> (infixr "\<le>\<^sub>s" 100) where
  "Leq\<^sub>s x y \<equiv> x \<le> y"

definition Imp\<^sub>s :: "formula\<^sub>s \<Rightarrow> formula\<^sub>s \<Rightarrow> formula\<^sub>s" (infixr "\<rightarrow>\<^sub>s" 25) where
  "\<phi> \<rightarrow>\<^sub>s \<psi> \<equiv> \<phi> \<longrightarrow> \<psi>"
definition Not\<^sub>s :: "formula\<^sub>s \<Rightarrow> formula\<^sub>s" ("\<not>\<^sub>s_" [40] 40) where
  "\<not>\<^sub>s\<phi> \<equiv> \<not>\<phi>"

definition Valid\<^sub>s :: "formula\<^sub>s \<Rightarrow> bool" ("\<Turnstile>\<^sub>s_" [10] 10) where
  "\<Turnstile>\<^sub>s \<phi> \<equiv> \<phi>"

definition And\<^sub>s :: "formula\<^sub>s \<Rightarrow> formula\<^sub>s \<Rightarrow> formula\<^sub>s" (infixr "\<and>\<^sub>s" 25) where
  "\<phi> \<and>\<^sub>s \<psi> \<equiv> \<not>\<^sub>s(\<phi> \<rightarrow>\<^sub>s \<not>\<^sub>s\<psi>)"

lemma "\<Turnstile>\<^sub>s x +\<^sub>s y =\<^sub>s y +\<^sub>s x"
  by (simp add: Valid\<^sub>s_def Add\<^sub>s_def Equal\<^sub>s_def)
lemma "\<Turnstile>\<^sub>s (0\<^sub>s \<le>\<^sub>s x) \<rightarrow>\<^sub>s (y \<le>\<^sub>s y +\<^sub>s x)"
  by (simp add: Valid\<^sub>s_def Add\<^sub>s_def Imp\<^sub>s_def Leq\<^sub>s_def Zero\<^sub>s_def)
lemma "\<Turnstile>\<^sub>s (x \<le>\<^sub>s y \<and>\<^sub>s y \<le>\<^sub>s x) \<rightarrow>\<^sub>s (x =\<^sub>s y)"
  by (simp add: Valid\<^sub>s_def And\<^sub>s_def Not\<^sub>s_def Equal\<^sub>s_def Imp\<^sub>s_def Leq\<^sub>s_def)

text\<open>Note: in this case, our language is completely contained in unmodified HOL, so we could
     just have used that:\<close>

lemma "(x::int) + y = y + x"
  by auto
lemma "(0::int) \<le> x \<longrightarrow> (y \<le> y + x)"
  by auto
lemma "(x::int) \<le> y \<and> y \<le> x \<longrightarrow> x = y"
  by auto

text\<open>Note that we need to force the type @{typ int}, since addition and less-than in Isabelle
     are generic for any group and order (for which our theorems may not hold).\<close>

text\<open>Things become more interesting in an actual extension of HOL, e.g. to higher-order modal logic.\<close>

end