theory T5b_Choice_Operators
  imports Main
begin

text\<open>Isabelle/HOL comes with two flavours of choice operators for indefinite and definite choice.\<close>

section\<open>Hilbert Epsilon - Indefinite Choice\<close>

text\<open>
     The indefinite choice operator or Hilbert Epsilon Operator allows to choose a term
     with some given property, if there is one, or denotes an arbitrary object, if there
     is none.
     Note: the indefinite choice operator is equivalent to the Axiom of Choice!
\<close>

term "Eps" \<comment> \<open>As a function the operator is called @{term Eps} with type
              @{typ \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a\<close>}, i.e. it takes a "predicate" on type @{typ 'a}
              and yields an object of type @{typ 'a}\<close>
term "SOME x . \<phi> x" \<comment> \<open>With binder syntax it's written as \<open>SOME x\<close> such that \<open>\<phi> x\<close>.\<close>

text\<open>The following is the only axiom needed for the choice operator:\<close>

lemma \<open>P x \<Longrightarrow> P (SOME x . P x)\<close>
  using someI.

text\<open>So if we know that @{prop \<open>P x\<close>} for some @{term x}, then @{term \<open>SOME x . P x\<close>} has the
     property P. Equivalently:\<close>

lemma \<open>(\<exists> x . P x) = P (SOME x . P x)\<close>
  by (metis someI)

text\<open>If there is no object with property @{term P}, @{term \<open>SOME x . P x\<close>} denotes an arbitrary
     object, which might have property @{term P}, but also might not have property @{term P}, i.e.
     we get both models and countermodels:\<close>
lemma \<open>\<not>(\<exists> x . P x) \<Longrightarrow> P (SOME x . P x)\<close>
  nitpick[user_axioms, expect=genuine] \<comment> \<open>countermodel\<close>
  nitpick[satisfy, user_axioms, expect=genuine] \<comment> \<open>model\<close>
  oops

section\<open>Definite Choice Operator\<close>

text\<open>The definite choice Operator is similar to definite descriptions \<open>\<iota>\<close> in object theory:
     It denotes \<^emph>\<open>the\<close> unique object that has some property, if there is a unique such object -
     however, if there is no unique such object, it still denotes, but similarly to the indefinite
     choice operator it then denotes an arbitrary object.\<close>

term "The" \<comment> \<open>As a function, definite choice is called @{term The},
               again of type @{typ \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a\<close>}\<close>
term \<open>THE x . \<phi> x\<close> \<comment> \<open>With binder notation it's written as \<open>THE x\<close>, s.t. \<open>\<phi> x\<close>.\<close>

text\<open>Due to the extensionality of HOL, the following is the only axiom we need:\<close>

lemma \<open>(THE x . x = a) = a\<close>
  using the_eq_trivial.

text\<open>This works, since whenever there is a unique object with some property, having that property
     is identical to being the object that has that property and the axiom can be applied using
     substitution.\<close>

lemma \<open>((\<exists>!x . \<phi> x) \<and> \<phi> a) \<longrightarrow> ((THE x . \<phi> x) = a)\<close>
  by (simp add: ex1_iff_ex_Uniq the1_equality')

text\<open>Note that the converse of the above has countermodels!\<close>
lemma \<open>((THE x . \<phi> x) = a) \<longrightarrow> ((\<exists>!x . \<phi> x) \<and> \<phi> a)\<close>
  nitpick[expect=genuine]
  nitpick[satisfy,expect=genuine] \<comment> \<open>It also has models\<close>
  oops

section\<open>The @{typ \<open>'a option\<close>} Type\<close>

text\<open>As any functional programming logic, Isabelle comes with an @{typ \<open>'a option\<close>} type, which
     can either be @{term \<open>Some (x::'a)\<close>} or @{term None}.
     You can ctrl-click \<open>option\<close> in @{typ \<open>'a option\<close>} to see that it is simply defined as a @{command datatype}
     with two constructors @{term \<open>Some\<close>} and @{term None}\<close>

text\<open>Using the @{typ \<open>'a option\<close>} type and the description operators, we can define modified
     choice operators, that will mimic "failing to denote", if the respective condition fails,
     by choosing @{term None} in that case:\<close>

subsection\<open>Indefinite Choice\<close>

definition SomeIfExists :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a option\<close> (binder \<open>SOMEOPT\<close> 100) where
  \<open>SOMEOPT x . \<phi> x \<equiv> (if \<exists> x . \<phi> x then Some (SOME x . \<phi> x) else None)\<close>

text\<open>We can derive some properties:\<close>

lemma SomeOpt_None_simp[simp]: \<open>((SOMEOPT x . \<phi> x) = None) = (\<nexists> x . \<phi> x)\<close>
  by (simp add: SomeIfExists_def)
lemma SomeOpt_Not_None_simp[simp]: \<open>((SOMEOPT x . \<phi> x) \<noteq> None) = (\<exists> x . \<phi> x)\<close>
  by simp

lemma SomeOpt_Some_witness:
  assumes \<open>\<exists> x . \<phi> x\<close>
  obtains y where \<open>SOMEOPT x . \<phi> x = Some y\<close> and \<open>\<phi> y\<close>
  by (simp add: SomeIfExists_def assms someI_ex)

text\<open>If our new operator "denotes", i.e. maps to @{term Some} object, that object
     has the desired property.\<close>
lemma \<open>(SOMEOPT x . \<phi> x = Some y) \<longrightarrow> (\<phi> y)\<close>
  by (metis SomeIfExists_def option.distinct(1) option.inject someI_ex)

text\<open>Conversely, if some object has the desired property, we know that the operator "denotes",
     but if there is more than one object with the property it might denote a different one!\<close>
lemma \<open>(\<phi> y) \<longrightarrow> (\<exists>z . SOMEOPT x . \<phi> x = Some z)\<close>
  by (simp add: SomeIfExists_def)

lemma \<open>(\<phi> y) \<longrightarrow> (SOMEOPT x . \<phi> x = Some y)\<close>
  nitpick[expect=genuine] \<comment> \<open>Counterexample! There might be more than one object, s.t. @{term \<phi>}\<close>
  oops

text\<open>We will later use this kind of operator to model object theory's lambda expressions!\<close>

subsection\<open>Definite Choice\<close>

definition TheIfExists :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a option\<close> (binder \<open>THEOPT\<close> 100) where
  \<open>THEOPT x . \<phi> x \<equiv> (if \<exists>! x . \<phi> x then Some (THE x . \<phi> x) else None)\<close>

text\<open>We can derive some properties:\<close>

lemma TheOpt_None_simp[simp]: \<open>((THEOPT x . \<phi> x) = None) = (\<nexists>! x . \<phi> x)\<close>
  by (simp add: TheIfExists_def)
lemma TheOpt_Not_None_simp[simp]: \<open>((THEOPT x . \<phi> x) \<noteq> None) = (\<exists>! x . \<phi> x)\<close>
  by simp

lemma TheOpt_Some_witness:
  assumes \<open>\<exists>! x . \<phi> x\<close>
  obtains y where \<open>THEOPT x . \<phi> x = Some y\<close> and \<open>\<phi> y\<close> and \<open>\<And> s . \<phi> s \<Longrightarrow> s = y\<close>
  by (metis TheIfExists_def assms the_equality)

lemma TheOpt_Eq: \<open>(THEOPT x . \<phi> x = Some y) = (\<phi> y \<and> (\<forall> z . \<phi> z \<longrightarrow> y = z))\<close>
  by (metis TheIfExists_def option.distinct(1) option.inject the_equality)

text\<open>Or equivalently:\<close>

lemma \<open>(Some y = THEOPT x . \<phi> x) = (\<forall> z . \<phi> z \<longleftrightarrow> z = y)\<close>
  by (metis TheOpt_Eq)

text\<open>Compare with object theory's axiom for definite descriptions:
     \<open>(y \<^bold>= \<iota>x(\<phi>) \<equiv> \<forall>x (\<A>\<phi> \<equiv> x = y)\<close>\<close>

text\<open>We will later model definite descriptions with this operator.\<close>

end